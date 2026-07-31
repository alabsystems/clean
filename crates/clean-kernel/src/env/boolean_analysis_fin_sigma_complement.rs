// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Step toward the 2-CYCLE branch of `Fin.sum_reindex_involution` (kkl
//! retirement): the **σ'' complement restriction** of an involution that SWAPS
//! the top with an interior point.
//!
//! Given an involution `σ : Fin (k+1) → Fin (k+1)` with `σ (last k) =
//! Fin.castSucc k p` for some `p : Fin k` (so by the involution `σ (castSucc k
//! p) = last k`), the (last, castSucc p) orbit is a 2-cycle.  Removing that
//! 2-cycle leaves an involution on the complement, which we encode as a function
//! `σ'' : Fin k → Fin k`:
//!
//! ```text
//! Fin.sigmaComplement :
//!   (k)(σ : Fin (k+1) → Fin (k+1))(hinv : ∀ x, σ (σ x) = x)
//!     (p : Fin k)(hcase : σ (last k) = Fin.castSucc k p) → Fin k → Fin k
//! ```
//!
//! Dispatch on `Nat.decEq (Fin.val j) (Fin.val p)`:
//! - `val j = val p` (i.e. `j = p`): `σ'' j := j` (p becomes a FIXED point of the
//!   complement — the orbit collapses).
//! - `val j ≠ val p`: `σ (castSucc j) ≠ last k` (else applying `σ` forces
//!   `castSucc j = castSucc p`, hence `j = p`), so `val (σ (castSucc j)) < k`,
//!   and `σ'' j := Fin.mk k (val (σ (castSucc j))) hlt` — exactly the
//!   `sigmaRestrict` `val`-arithmetic.
//!
//! Deliverables (all constructive, empty admitted-axiom closure):
//! - `Fin.sigmaComplement_partner` — `σ (castSucc k p) = last k`.
//! - `Fin.sigmaComplement_ne_last` — `val j ≠ val p → σ (castSucc j) ≠ last k`.
//! - `Fin.sigmaComplement` — the σ'' map.
//! - `Fin.sigmaComplement_coh_ne` — `val j ≠ val p →
//!     σ (castSucc j) = castSucc (σ'' j)` (the off-`p` coherence).
//! - `Fin.sigmaComplement_fix_p` — `σ'' p = p`.
//! - `Fin.sigmaComplement_involutive` — `σ'' (σ'' j) = j`.
//!
//! These feed the 2-cycle inductive step (`Fin.sum_reindex_twocycle_step`):
//! `Fin.sum_succ` peels `last` on both sides, `Fin.sum_remove` at `p` pulls the
//! orbit partner out of each `Σ_k`, the complement sums match by `Fin.sum_congr`
//! (the off-`p` coherence — NO reindex needed), and the IH at `σ''` on `Fin k`
//! collapses the residual.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the σ'' complement lemmas.
pub(super) struct SigmaComplementConsts {
    pub(super) nat: Expr,
    pub(super) nat_succ: Expr,
    pub(super) fin: Expr,
    pub(super) fin_mk: Expr,
    pub(super) fin_val: Expr,
    pub(super) fin_islt: Expr,
    pub(super) fin_cast_succ: Expr,
    pub(super) fin_last: Expr,
    pub(super) fin_eq_of_val: Expr,
    pub(super) cast_succ_inj: Expr,
    pub(super) cast_succ_ne_last: Expr,
    pub(super) nat_deceq: Expr,
    pub(super) nat_le_of_ss: Expr,
    pub(super) nat_lt_of_le_ne: Expr,
    pub(super) decidable: Expr,
    pub(super) decidable_rec0: Expr, // Decidable.rec.{0} — Prop motive
    pub(super) decidable_rec1: Expr, // Decidable.rec.{1} — Fin-valued motive
    pub(super) false_c: Expr,
    pub(super) eq1: Expr,
    pub(super) eq_refl_nat: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_trans: Expr,
    pub(super) congr_arg: Expr,
}

impl SigmaComplementConsts {
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
            cast_succ_inj: k("Fin.castSucc_inj"),
            cast_succ_ne_last: k("Fin.castSucc_ne_last"),
            nat_deceq: k("Nat.decEq"),
            nat_le_of_ss: k("Nat.le_of_succ_le_succ"),
            nat_lt_of_le_ne: k("Nat.lt_of_le_of_ne"),
            decidable: k("Decidable"),
            decidable_rec0: Expr::const_(Name::from_string("Decidable.rec"), vec![l0.clone()]),
            decidable_rec1: Expr::const_(Name::from_string("Decidable.rec"), vec![l1.clone()]),
            false_c: k("False"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_nat: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
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
    #[cfg(test)]
    pub(super) fn app1(&self, f: &Expr, x: Expr) -> Expr {
        Expr::app(f.clone(), x)
    }

    /// `Fin.sigmaComplement k σ hinv p hcase j` — σ'' applied at `j`.
    pub(super) fn sigma_pp(
        &self,
        k: &Expr,
        sigma: &Expr,
        hinv: &Expr,
        p: &Expr,
        hcase: &Expr,
        j: &Expr,
    ) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sigmaComplement"), vec![]),
            [
                k.clone(),
                sigma.clone(),
                hinv.clone(),
                p.clone(),
                hcase.clone(),
                j.clone(),
            ],
        )
    }
}

include!("boolean_analysis_fin_sigma_complement_build.rs");

impl Environment {
    /// Register the σ'' complement bundle: `Fin.sigmaComplement_partner`,
    /// `Fin.sigmaComplement_ne_last`, `Fin.sigmaComplement`,
    /// `Fin.sigmaComplement_coh_ne`, `Fin.sigmaComplement_fix_p`,
    /// `Fin.sigmaComplement_involutive`. All constructive, empty axiom closure.
    /// Idempotent.
    pub(crate) fn register_fin_sigma_complement(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.sigmaComplement_involutive"))
            .is_some()
        {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin()?;
        self.init_lt()?;
        self.init_decidable()?;
        self.register_nat_dec_eq_proof()?; // Nat.decEq
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_fin_index_lemmas()?; // Fin.castSucc_inj, Fin.castSucc_ne_last + ensures
        self.init_nat_totality_proofs()?; // Nat.lt_of_le_of_ne
        self.register_nat_le_of_succ_le_succ_theorem()?; // Nat.le_of_succ_le_succ

        let c = SigmaComplementConsts::new();

        // 1. partner : σ (castSucc p) = last
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaComplement_partner"),
            level_params: vec![],
            type_: partner_type(&c),
            value: partner_value(&c),
        })?;

        // 2. ne_last : val j ≠ val p → σ (castSucc j) = last → False
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaComplement_ne_last"),
            level_params: vec![],
            type_: ne_last_type(&c),
            value: ne_last_value(&c),
        })?;

        // 3. the σ'' map (Definition).
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.sigmaComplement"),
            level_params: vec![],
            type_: complement_type(&c),
            value: complement_value(&c),
            is_reducible: true,
        })?;

        // 4. coh_ne : val j ≠ val p → σ (castSucc j) = castSucc (σ'' j)
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaComplement_coh_ne"),
            level_params: vec![],
            type_: coh_ne_type(&c),
            value: coh_ne_value(&c),
        })?;

        // 4a. eq_self : val j = val p → σ'' j = j  (helper for fix_p + involutive)
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaComplement_eq_self"),
            level_params: vec![],
            type_: eq_self_type(&c),
            value: eq_self_value(&c),
        })?;

        // 4b. ne_p : val j ≠ val p → val (σ'' j) ≠ val p  (helper for involutive)
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaComplement_ne_p"),
            level_params: vec![],
            type_: ne_p_type(&c),
            value: ne_p_value(&c),
        })?;

        // 5. fix_p : σ'' p = p
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaComplement_fix_p"),
            level_params: vec![],
            type_: fix_p_type(&c),
            value: fix_p_value(&c),
        })?;

        // 6. involutive : σ'' (σ'' j) = j
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.sigmaComplement_involutive"),
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
    fn test_fin_sigma_complement_bundle_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_sigma_complement().expect("register");
        env.register_fin_sigma_complement().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        for (name, is_def) in [
            ("Fin.sigmaComplement_partner", false),
            ("Fin.sigmaComplement_ne_last", false),
            ("Fin.sigmaComplement", true),
            ("Fin.sigmaComplement_coh_ne", false),
            ("Fin.sigmaComplement_fix_p", false),
            ("Fin.sigmaComplement_involutive", false),
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
