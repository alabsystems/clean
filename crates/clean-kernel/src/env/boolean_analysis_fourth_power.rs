// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — B5 fourth-power even-pair.
//!
//! The equational layer the (2,4)-hypercontractivity B5 step consumes. The
//! fourth-power even-pair identity
//!   `(A+B)⁴ + (A−B)⁴ = 2·A⁴ + 12·A²·B² + 2·B⁴`
//! factors through the **parallelogram law**
//!   `(m+c)² + (m−c)² = 2·m² + 2·c²`   (`Rat.add_sq_add_sub_sq`)
//! at `m := A²+B²`, `c := 2·A·B`, since `(A±B)² = (A²+B²) ± 2AB`. This commit
//! lands the parallelogram law; the final `m`/`c` substitution + collection to
//! `2A⁴+12A²B²+2B⁴` is the run-7 residual (see module-level note in
//! `boolean_analysis_fourth_power_proofs.rs`).
//!
//! Every lemma is a kernel-checked `Declaration::Theorem` registered through the
//! CHECKED `add_decl` path, built from the run-2/3 square identities
//! (`Rat.add_sq`, `Rat.sub_sq`) and the constructive `Rat` additive surface.
//! Numerals are `Rat.one`-sums (`2 := 1+1`), so closed forms are reached by
//! chaining proven ring lemmas, never refl-reduction. Because every dependency
//! is `ProofQuality::Constructive` (empty domain-axiom closure), so is the
//! parallelogram law.

use super::boolean_analysis_fourth_power_assemble_proofs::{
    add_sq_regroup_type, build_add_sq_regroup_proof, build_sub_sq_regroup_proof,
    sub_sq_regroup_type,
};
use super::boolean_analysis_fourth_power_even_pair_proofs::{
    build_fourth_power_even_pair_proof, fourth_power_even_pair_type,
};
use super::boolean_analysis_fourth_power_expand_proofs::{
    build_fourth_power_even_pair_expanded_proof, fourth_power_even_pair_expanded_type,
};
use super::boolean_analysis_fourth_power_proofs::{
    add_sq_add_sub_sq_type, build_add_sq_add_sub_sq_proof,
};
use super::boolean_analysis_ring_identities_proofs::RingConsts;
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize the Bonami-Beckner B5 fourth-power even-pair layer.
    ///
    /// Registers the parallelogram law `Rat.add_sq_add_sub_sq` as a
    /// kernel-checked `Declaration::Theorem`. Idempotent.
    ///
    /// Depends on `init_boolean_analysis_ring_identities`, which provides the
    /// constructive square identities `Rat.add_sq` / `Rat.sub_sq` and the
    /// `Rat` ring/additive surface this layer chains over.
    pub fn init_boolean_analysis_fourth_power(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_fourth_power_init {
            return Ok(());
        }
        self.init_boolean_analysis_ring_identities()?;
        // `Rat.mul_mul_mul_comm` ((a·b)·(c·d) = (a·c)·(b·d)) is the regrouper the
        // expanded form uses to fold `C·C = (2·(A·B))² = (2·2)·(A²·B²)`.
        self.register_rat_mul_mul_mul_comm_theorem()?;

        let c = RingConsts::new();
        self.register_rat_add_sq_add_sub_sq(&c)?;
        self.register_rat_add_sq_regroup(&c)?;
        self.register_rat_sub_sq_regroup(&c)?;
        self.register_rat_fourth_power_even_pair(&c)?;
        self.register_rat_fourth_power_even_pair_expanded(&c)?;

        self.boolean_analysis_fourth_power_init = true;
        Ok(())
    }

    /// `Rat.sub_sq_regroup : ∀ A B,
    ///     (A−B)·(A−B) = (A·A + B·B) + (1+1)·(A·(−B))`.
    ///
    /// The `(A−B)²` mirror of `Rat.add_sq_regroup`. Restates `Rat.sub_sq`'s RHS
    /// `(A·A + 2·(A·(−B))) + B·B` in the `m + c` shape (commute the trailing
    /// `B·B` past the cross term), with cross term `2·(A·(−B))` — the negative of
    /// `add_sq_regroup`'s. The two regroups feed the parallelogram law at
    /// `m := A·A + B·B`. Constructive (empty domain-axiom closure).
    fn register_rat_sub_sq_regroup(&mut self, c: &RingConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_sq_regroup");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = sub_sq_regroup_type(c);
        let value = build_sub_sq_regroup_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_sq_regroup : ∀ A B,
    ///     (A+B)·(A+B) = (A·A + B·B) + (1+1)·(A·B)`.
    ///
    /// Restates `Rat.add_sq`'s RHS `(A·A + 2·(A·B)) + B·B` in the `m + c` shape
    /// (`m = A²+B²`, `c = 2·A·B`) the parallelogram law's binders expect, by
    /// commuting the trailing `B·B` past the cross term (`add_assoc` +
    /// `add_comm`). The bridge that connects `(A+B)⁴` to
    /// `Rat.add_sq_add_sub_sq`. Constructive (empty domain-axiom closure).
    fn register_rat_add_sq_regroup(&mut self, c: &RingConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_sq_regroup");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = add_sq_regroup_type(c);
        let value = build_add_sq_regroup_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.add_sq_add_sub_sq : ∀ m c,
    ///     (m+c)·(m+c) + (m−c)·(m−c) = (1+1)·(m·m) + (1+1)·(c·c)`.
    ///
    /// The parallelogram law. Rewrites each square via `Rat.add_sq` /
    /// `Rat.sub_sq`, folds `2·(m·(−c)) = −(2·(m·c))` through `Rat.mul_neg`, then
    /// the additive-cancellation helper collapses the cross terms, leaving
    /// `2·m² + 2·c²`. Constructive (empty domain-axiom closure).
    fn register_rat_add_sq_add_sub_sq(&mut self, c: &RingConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_sq_add_sub_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = add_sq_add_sub_sq_type(c);
        let value = build_add_sq_add_sub_sq_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.fourth_power_even_pair : ∀ A B,
    ///     ((A+B)·(A+B))·((A+B)·(A+B)) + ((A−B)·(A−B))·((A−B)·(A−B))
    ///       = (1+1)·(M·M) + (1+1)·(C·C)`
    /// with `M := A·A + B·B`, `C := (1+1)·(A·B)`.
    ///
    /// The B5 keystone. `Rat.add_sq_regroup` / `Rat.sub_sq_regroup` restate the
    /// inner squares as `M+C` / `M+(−C)` (folding `2·(A·(−B)) = −C` through
    /// `Rat.mul_neg`); the fourth powers become `(M±C)·(M±C)` by congruence;
    /// `Rat.add_sq_add_sub_sq M C` (the parallelogram law) closes to
    /// `2·M² + 2·C²`. Constructive (empty domain-axiom closure).
    fn register_rat_fourth_power_even_pair(&mut self, c: &RingConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.fourth_power_even_pair");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = fourth_power_even_pair_type(c);
        let value = build_fourth_power_even_pair_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.fourth_power_even_pair_expanded : ∀ A B,
    ///     ((A+B)·(A+B))·((A+B)·(A+B)) + ((A−B)·(A−B))·((A−B)·(A−B))
    ///       = ((1+1)·A⁴ + (1+1)·B⁴)
    ///         + ((1+1)·(1+1) + (1+1)·((1+1)·(1+1)))·(A²·B²)`
    /// with `A⁴ := (A·A)·(A·A)`, `B⁴ := (B·B)·(B·B)`, `A²·B² := (A·A)·(B·B)`.
    ///
    /// The monomial normal form `2A⁴ + 12A²B² + 2B⁴` of the even-pair identity:
    /// expands the keystone RHS `2·M² + 2·C²` via `Rat.add_sq_regroup` (for
    /// `M·M`), `Rat.mul_mul_mul_comm` (for `C·C = (2·2)·A²B²`), `Rat.left_distrib`
    /// / `Rat.mul_assoc` (distribute the outer `2·`s), and one
    /// `Rat.right_distrib` to gather the two cross terms into the single
    /// coefficient `(2·2) + 2·(2·2)` — the honest `4 + 8` split. Constructive
    /// (empty domain-axiom closure).
    fn register_rat_fourth_power_even_pair_expanded(
        &mut self,
        c: &RingConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.fourth_power_even_pair_expanded");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = fourth_power_even_pair_expanded_type(c);
        let value = build_fourth_power_even_pair_expanded_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if the B5 fourth-power even-pair layer has been initialized.
    #[cfg(test)]
    pub(crate) fn has_boolean_analysis_fourth_power(&self) -> bool {
        self.boolean_analysis_fourth_power_init
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Lemmas registered by this module (run 6 + run 7).
    const TOOLKIT: &[&str] = &[
        "Rat.add_sq_add_sub_sq",
        "Rat.add_sq_regroup",
        "Rat.sub_sq_regroup",
        "Rat.fourth_power_even_pair",
        "Rat.fourth_power_even_pair_expanded",
    ];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_fourth_power()
            .expect("init_boolean_analysis_fourth_power should succeed");
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
        env.init_boolean_analysis_fourth_power()
            .expect("first init");
        env.init_boolean_analysis_fourth_power()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_fourth_power());
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

    /// The parallelogram law has an empty domain-axiom closure and is therefore
    /// classified `ProofQuality::Constructive` — the square identities and the
    /// `Rat` additive surface it chains over are all constructive over the
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
