// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Step 1 of the `Fin.sum_reindex_involution` keystone (kkl retirement): the
//! **σ' restriction** of a top-fixing involution.
//!
//! Given an involution `σ : Fin (k+1) → Fin (k+1)` with `σ (last k) = last k`,
//! `σ` restricts to a function `σ' : Fin k → Fin k`:
//!
//! ```text
//! Fin.sigmaRestrict : (k : Nat) (σ : Fin (k+1) → Fin (k+1))
//!   → (∀ jx, σ (σ jx) = jx) → (σ (last k) = last k) → Fin k → Fin k
//! Fin.sigmaRestrict k σ hinv hfix j
//!   := Fin.mk k (Fin.val (k+1) (σ (castSucc k j))) (hlt …)
//! ```
//!
//! The deliverables (all constructive, empty admitted-axiom closure):
//!
//! - `Fin.sigmaRestrict_ne_last` — `σ (castSucc k j) ≠ last k`.  If they were
//!   equal then `σ (castSucc j) = last = σ (last)`, and applying `σ` (using the
//!   involution) gives `castSucc j = last`, contradicting `castSucc_ne_last`.
//! - `Fin.sigmaRestrict` — the restriction map.  Its `val` bound `hlt :
//!   Fin.val (k+1) (σ (castSucc j)) < k` comes from `Fin.isLt` (`< k+1`, hence
//!   `≤ k` via `le_of_succ_le_succ`) + `val ≠ k` (else the element would be
//!   `last k`, contradicting the above).
//! - `Fin.sigmaRestrict_coherence` — `σ (castSucc k j) = castSucc k (σ' j)`,
//!   by `Fin.eq_of_val_eq` (both sides have `val ≡ Fin.val (σ (castSucc j))`).
//! - `Fin.sigmaRestrict_involutive` — `σ' (σ' j) = j`, at the `val` level from
//!   the coherence + the `σ` involution.
//!
//! These are exactly the hypotheses `Fin.sum_reindex_fixed_last` consumes, so
//! the fixed-point branch of the keystone is closed by feeding σ' + coherence
//! into that lemma and recursing the IH at `σ'` on `Fin k`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the σ' restriction lemmas.
pub(super) struct SigmaRestrictConsts {
    pub(super) nat: Expr,
    pub(super) nat_succ: Expr,
    pub(super) fin: Expr,
    pub(super) fin_mk: Expr,
    pub(super) fin_val: Expr,
    pub(super) fin_islt: Expr,
    pub(super) fin_cast_succ: Expr,
    pub(super) fin_last: Expr,
    pub(super) fin_eq_of_val: Expr,
    pub(super) cast_succ_ne_last: Expr,
    pub(super) nat_le_of_ss: Expr,
    pub(super) nat_lt_of_le_ne: Expr,
    pub(super) false_c: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) false_elim_l1: Expr,
    pub(super) eq1: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_trans: Expr,
    pub(super) congr_arg: Expr,
}

impl SigmaRestrictConsts {
    pub(super) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_succ: k("Nat.succ"),
            fin: k("Fin"),
            fin_mk: k("Fin.mk"),
            fin_val: k("Fin.val"),
            fin_islt: k("Fin.isLt"),
            fin_cast_succ: k("Fin.castSucc"),
            fin_last: k("Fin.last"),
            fin_eq_of_val: k("Fin.eq_of_val_eq"),
            cast_succ_ne_last: k("Fin.castSucc_ne_last"),
            nat_le_of_ss: k("Nat.le_of_succ_le_succ"),
            nat_lt_of_le_ne: k("Nat.lt_of_le_of_ne"),
            false_c: k("False"),
            #[cfg(test)]
            false_elim_l1: Expr::const_(Name::from_string("False.elim"), vec![l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    pub(super) fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    pub(super) fn cast_succ(&self, k: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [k.clone(), j.clone()])
    }
    pub(super) fn last(&self, k: &Expr) -> Expr {
        Expr::app(self.fin_last.clone(), k.clone())
    }
    pub(super) fn val(&self, n: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), x.clone()])
    }
    pub(super) fn eq_fin(&self, n: &Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.fin_of(n), l, r])
    }
    pub(super) fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    /// `σ x`.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pub(super) fn app1(&self, f: &Expr, x: Expr) -> Expr {
        Expr::app(f.clone(), x)
    }

    /// `Fin.sigmaRestrict k σ hinv hfix j` — the σ' restriction applied at `j`.
    pub(super) fn restrict(
        &self,
        k: &Expr,
        sigma: &Expr,
        hinv: &Expr,
        hfix: &Expr,
        j: &Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sigmaRestrict"), vec![]),
            [
                k.clone(),
                sigma.clone(),
                hinv.clone(),
                hfix.clone(),
                j.clone(),
            ],
        )
    }
}

include!("boolean_analysis_fin_sigma_restrict_build.rs");

impl Environment {
    /// Register the σ' restriction bundle: `Fin.sigmaRestrict_ne_last`,
    /// `Fin.sigmaRestrict`, `Fin.sigmaRestrict_coherence`,
    /// `Fin.sigmaRestrict_involutive`. All constructive, empty axiom closure.
    /// Idempotent.
    pub(crate) fn register_fin_sigma_restrict(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.sigmaRestrict_involutive"))
            .is_some()
        {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin()?;
        self.init_lt()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_fin_index_lemmas()?; // Fin.castSucc_ne_last + castSucc/last ensures
        self.init_nat_totality_proofs()?; // Nat.lt_of_le_of_ne
        self.register_nat_le_of_succ_le_succ_theorem()?; // Nat.le_of_succ_le_succ

        let c = SigmaRestrictConsts::new();

        // 1. Fin.sigmaRestrict_ne_last
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaRestrict_ne_last"),
            level_params: vec![],
            type_: ne_last_type(&c),
            value: ne_last_value(&c),
        })?;

        // 2. Fin.sigmaRestrict (the function — Definition).
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.sigmaRestrict"),
            level_params: vec![],
            type_: restrict_type(&c),
            value: restrict_value(&c),
            is_reducible: true,
        })?;

        // 3. Fin.sigmaRestrict_coherence
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaRestrict_coherence"),
            level_params: vec![],
            type_: coherence_type(&c),
            value: coherence_value(&c),
        })?;

        // 4. Fin.sigmaRestrict_involutive
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaRestrict_involutive"),
            level_params: vec![],
            type_: involutive_type(&c),
            value: involutive_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_sigma_restrict_bundle_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sigma_restrict().expect("register");
        env.register_fin_sigma_restrict().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for (name, is_def) in [
            ("Fin.sigmaRestrict_ne_last", false),
            ("Fin.sigmaRestrict", true),
            ("Fin.sigmaRestrict_coherence", false),
            ("Fin.sigmaRestrict_involutive", false),
        ] {
            let n = Name::from_string(name);
            let info = env.get_const(&n).expect("registered");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            let deps = env.axiom_deps(&n).expect("deps");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
            if is_def {
                assert_eq!(info.kind, ConstantKind::Definition);
            } else {
                assert_eq!(info.kind, ConstantKind::Theorem);
                assert!(matches!(
                    env.proof_quality(&n),
                    Some(ProofQuality::Constructive)
                ));
            }
        }
    }
}
