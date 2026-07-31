// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Head rigidity for applications, **multi-step** — the version
//! `stuck_app_rigidity.rs` had to drop.
//!
//! ```text
//! par_reduces_cd_star_rigid_app_inv :
//!   rigid_app_head (app f a) -> par_reduces_cd_star env (app f a) t
//!     -> StuckAppRedWitness env f a t
//! ```
//!
//! The single-step version over `whnf_stuck_head` landed earlier; its closure
//! lift was impossible because `whnf_stuck_head` is not preserved. Restating the
//! premise over `rigid_app_head` — which is preserved
//! (`rigid_preservation.rs`) — makes the induction go through: at each step the
//! head stays rigid, so the induction hypothesis applies to the reduct.
//!
//! Both premises now sit on the **whole application** rather than on its head.
//! `rigid_app_head` is closed under application, so `rigid_app_head (app f a)`
//! is the natural form, and it feeds the ι/δ immunity lemmas directly instead
//! of needing them restated at an application of a stuck head.
//!
//! Everything the earlier module established transfers: callers holding a
//! `whnf_stuck_head` (from `whnf_noredex_class`'s `stuck` arm) reach this
//! through `whnf_stuck_head_rigid`.
//!
//! `DerivedProved` throughout, empty axiom closures.

use crate::spec::core_spec::kexpr_discr::CD_STRUCTURAL_ARMS;
use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Application head rigidity over the preserved predicate.
    pub(super) fn add_rigid_app_inv(&mut self) -> Result<(), SpecError> {
        self.add_rigid_app_inv_step()?;
        self.add_rigid_app_inv_star()?;
        Ok(())
    }

    /// The eleven minor premises.
    fn rigid_app_inv_arms() -> String {
        let goal = |t: &str| format!("(StuckAppRedWitness env f a {t})");
        let motive_at = |p: &str, q: &str| {
            format!(
                "forall (f : KExpr) (a : KExpr), rigid_app_head (KExpr.app f a) -> \
                 Eq KExpr {p} (KExpr.app f a) -> {g}",
                g = goal(q)
            )
        };
        // Binder names are generated from the same table as their types, so a
        // referenced name cannot fail to be bound.
        let block = |idx: usize, proof_names: &[&str], ih_names: &[&str]| {
            let (payload, pairs, _src, _tgt) = CD_STRUCTURAL_ARMS[idx];
            let mut proofs = String::new();
            let mut ihs = String::new();
            for (slot, (from, to)) in pairs.iter().enumerate() {
                let pn = proof_names.get(slot).copied().unwrap_or("_");
                let inn = ih_names.get(slot).copied().unwrap_or("_");
                proofs.push_str(&format!("({pn} : par_reduces_cd env {from} {to}) "));
                ihs.push_str(&format!("({inn} : {}) ", motive_at(from, to)));
            }
            (payload, proofs, ihs)
        };
        let discriminate = |idx: usize| {
            let (payload, proofs, ihs) = block(idx, &[], &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[idx];
            format!(
                "(fun {payload} {proofs}{ihs}(f : KExpr) (a : KExpr) \
                 (_hr : rigid_app_head (KExpr.app f a)) \
                 (heq : Eq KExpr {src} (KExpr.app f a)) => \
                 kexpr_discr_t {g} {src} (KExpr.app f a) heq (Eq.refl Bool Bool.false)) ",
                g = goal(tgt)
            )
        };

        // refl
        let mut arms = format!(
            "(fun (e0 : KExpr) (f : KExpr) (a : KExpr) \
             (_hr : rigid_app_head (KExpr.app f a)) \
             (heq : Eq KExpr e0 (KExpr.app f a)) => \
             StuckAppRedWitness.mk env f a e0 f a heq \
             (par_reduces_cd_star.refl env f) (par_reduces_cd_star.refl env a)) "
        );

        // beta: the head would be a lambda, and a rigid head is not.
        {
            let (payload, proofs, ihs) = block(0, &[], &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[0];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(f : KExpr) (a : KExpr) \
                 (hr : rigid_app_head (KExpr.app f a)) \
                 (heq : Eq KExpr {src} (KExpr.app f a)) => \
                 rigid_app_head_not_lam f \
                 (rigid_app_head_app_inv (KExpr.app f a) hr f a \
                 (Eq.refl KExpr (KExpr.app f a))) \
                 {g} bA bbody \
                 (Eq.symm KExpr (KExpr.lam bA bbody) f \
                 (app_inj_fst (KExpr.lam bA bbody) barg f a heq))) ",
                g = goal(tgt)
            ));
        }

        // app: the substantive congruence.
        {
            let (payload, proofs, ihs) = block(1, &["hpf", "hpa"], &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[1];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(f : KExpr) (a : KExpr) \
                 (_hr : rigid_app_head (KExpr.app f a)) \
                 (heq : Eq KExpr {src} (KExpr.app f a)) => \
                 (fun (hf : Eq KExpr af f) (ha : Eq KExpr aa a) => \
                 StuckAppRedWitness.mk env f a {tgt} af2 aa2 \
                 (Eq.refl KExpr {tgt}) \
                 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd_star env z af2) \
                 af f hf (par_reduces_cd_star.step env af af2 af2 hpf \
                 (par_reduces_cd_star.refl env af2))) \
                 (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd_star env z aa2) \
                 aa a ha (par_reduces_cd_star.step env aa aa2 aa2 hpa \
                 (par_reduces_cd_star.refl env aa2)))) \
                 (app_inj_fst af aa f a heq) (app_inj_snd af aa f a heq)) "
            ));
        }

        // lam, pi, forall_, let_ : different heads.
        for idx in 2..6 {
            arms.push_str(&discriminate(idx));
        }

        // iota / delta: immunity at the whole application.
        for (ctor, envsel, immune, var) in [
            ("iota", "red_rec env", "rigid_app_iota_immune", "ie"),
            ("delta", "red_def env", "rigid_app_delta_immune", "de"),
        ] {
            arms.push_str(&format!(
                "(fun ({var} : KExpr) ({var}2 : KExpr) \
                 (hst : {ctor}_step ({envsel}) {var} {var}2) (f : KExpr) (a : KExpr) \
                 (hr : rigid_app_head (KExpr.app f a)) \
                 (heq : Eq KExpr {var} (KExpr.app f a)) => \
                 opt_none_ne_some_t KExpr {var}2 {g} \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
                 ({ctor}_reduct ({envsel}) (KExpr.app f a)) \
                 (OptionType.some KExpr {var}2) \
                 (Eq.symm (OptionType KExpr) ({ctor}_reduct ({envsel}) (KExpr.app f a)) \
                 (OptionType.none KExpr) ({immune} env (KExpr.app f a) hr)) \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq (OptionType KExpr) ({ctor}_reduct ({envsel}) z) \
                 (OptionType.some KExpr {var}2)) {var} (KExpr.app f a) heq hst))) ",
                g = goal(&format!("{var}2"))
            ));
        }

        // let_cong, proj
        arms.push_str(&discriminate(6));
        arms.push_str(&discriminate(7));

        arms
    }

    fn add_rigid_app_inv_step(&mut self) -> Result<(), SpecError> {
        let arms = Self::rigid_app_inv_arms();
        self.add_recursive_def(
            &format!(
                "def par_reduces_cd_rigid_app_inv (env : RedEnv) (p : KExpr) (q : KExpr) \
                 (h : par_reduces_cd env p q) : \
                 forall (f : KExpr) (a : KExpr), rigid_app_head (KExpr.app f a) -> \
                 Eq KExpr p (KExpr.app f a) -> StuckAppRedWitness env f a q := \
                 par_reduces_cd.rec env \
                 (fun (pp : KExpr) (qq : KExpr) (_h : par_reduces_cd env pp qq) => \
                 forall (f : KExpr) (a : KExpr), rigid_app_head (KExpr.app f a) -> \
                 Eq KExpr pp (KExpr.app f a) -> StuckAppRedWitness env f a qq) \
                 {arms}p q h"
            ),
            "par_reduces_cd_rigid_app_inv: single-step head rigidity for applications, with the \
             premise over the PRESERVED rigid_app_head rather than whnf_stuck_head. Same eleven \
             arms as its predecessor; the premise now sits on the whole application, which is \
             the natural form since rigid_app_head is closed under application and it feeds the \
             immunity lemmas directly. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_rigid_app_inv_star(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def par_reduces_cd_star_rigid_app_inv (env : RedEnv) (p : KExpr) (t : KExpr) \
             (h : par_reduces_cd_star env p t) : \
             forall (f : KExpr) (a : KExpr), rigid_app_head (KExpr.app f a) -> \
             Eq KExpr p (KExpr.app f a) -> StuckAppRedWitness env f a t := \
             par_reduces_cd_star.rec env \
             (fun (pp : KExpr) (qq : KExpr) (_h : par_reduces_cd_star env pp qq) => \
             forall (f : KExpr) (a : KExpr), rigid_app_head (KExpr.app f a) -> \
             Eq KExpr pp (KExpr.app f a) -> StuckAppRedWitness env f a qq) \
             (fun (e0 : KExpr) (f : KExpr) (a : KExpr) \
             (_hr : rigid_app_head (KExpr.app f a)) \
             (heq : Eq KExpr e0 (KExpr.app f a)) => \
             StuckAppRedWitness.mk env f a e0 f a heq \
             (par_reduces_cd_star.refl env f) (par_reduces_cd_star.refl env a)) \
             (fun (e0 : KExpr) (e1 : KExpr) (e3 : KExpr) \
             (hstep : par_reduces_cd env e0 e1) \
             (_hstar : par_reduces_cd_star env e1 e3) \
             (ih : forall (f : KExpr) (a : KExpr), rigid_app_head (KExpr.app f a) -> \
             Eq KExpr e1 (KExpr.app f a) -> StuckAppRedWitness env f a e3) \
             (f : KExpr) (a : KExpr) (hr : rigid_app_head (KExpr.app f a)) \
             (heq : Eq KExpr e0 (KExpr.app f a)) => \
             StuckAppRedWitness.rec env f a e1 \
             (fun (_w : StuckAppRedWitness env f a e1) => StuckAppRedWitness env f a e3) \
             (fun (f1 : KExpr) (a1 : KExpr) (he1 : Eq KExpr e1 (KExpr.app f1 a1)) \
             (hf1 : par_reduces_cd_star env f f1) (ha1 : par_reduces_cd_star env a a1) => \
             StuckAppRedWitness.rec env f1 a1 e3 \
             (fun (_w2 : StuckAppRedWitness env f1 a1 e3) => StuckAppRedWitness env f a e3) \
             (fun (f2 : KExpr) (a2 : KExpr) (he2 : Eq KExpr e3 (KExpr.app f2 a2)) \
             (hf2 : par_reduces_cd_star env f1 f2) (ha2 : par_reduces_cd_star env a1 a2) => \
             StuckAppRedWitness.mk env f a e3 f2 a2 he2 \
             (par_reduces_cd_star_trans env f f1 f2 hf1 hf2) \
             (par_reduces_cd_star_trans env a a1 a2 ha1 ha2)) \
             (ih f1 a1 \
             (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) e1 \
             (KExpr.app f1 a1) he1 \
             (rigid_app_head_preserved env e0 e1 hstep \
             (Eq.substType KExpr (fun (z : KExpr) => rigid_app_head z) \
             (KExpr.app f a) e0 (Eq.symm KExpr e0 (KExpr.app f a) heq) hr))) \
             he1)) \
             (par_reduces_cd_rigid_app_inv env e0 e1 hstep f a hr heq)) \
             p t h",
            "par_reduces_cd_star_rigid_app_inv: MULTI-STEP head rigidity for applications — the \
             version stuck_app_rigidity.rs had to drop. What unblocks it is exactly \
             rigid_app_head_preserved: at each step the head stays rigid, so the induction \
             hypothesis applies to the reduct. Concretely the recursive call transports the \
             original rigidity along the step (preserved) and then along the witness's shape \
             equation, which is the obligation whnf_stuck_head could not discharge. The two \
             witnesses are unpacked and the component reductions composed with \
             par_reduces_cd_star_trans. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rigid_app_inv_arms_has_eleven_minor_premises() {
        let arms = Specification::rigid_app_inv_arms();
        let minors = arms.matches("(fun ").count()
            - arms.matches("(fun (z : KExpr)").count()
            - arms.matches("(fun (hf :").count();
        assert_eq!(minors, 11, "expected 11 minor premises, got {minors}");
    }

    #[test]
    fn test_rigid_app_inv_arms_declaration_order() {
        let arms = Specification::rigid_app_inv_arms();
        let landmarks = [
            "(fun (e0 : KExpr)",
            "rigid_app_head_not_lam f",
            "app_inj_snd af aa f a",
            "(KExpr.lam lty lbody)",
            "(KExpr.pi pdom pbody)",
            "(KExpr.forall_ qdom qbody)",
            "(KExpr.let_ zty zval zbody)",
            "rigid_app_iota_immune",
            "rigid_app_delta_immune",
            "(KExpr.let_ cty cval cbody)",
            "(KExpr.proj ps pi2 psub)",
        ];
        let mut cursor = 0usize;
        for (position, mark) in landmarks.iter().enumerate() {
            let found = arms[cursor..].find(mark).unwrap_or_else(|| {
                panic!("minor premise {position} ({mark}) missing/out of order")
            });
            cursor += found + mark.len();
        }
    }

    #[test]
    fn test_rigid_app_inv_arms_bind_proofs_and_ihs() {
        let arms = Specification::rigid_app_inv_arms();
        let proofs = arms.matches(" : par_reduces_cd env ").count();
        let ihs = arms
            .matches("(_ : forall (f : KExpr) (a : KExpr), rigid_app_head")
            .count();
        assert_eq!(
            proofs, 18,
            "18 recursive premises across the eight structural arms"
        );
        assert_eq!(ihs, 18, "one induction hypothesis each");
    }

    /// The immunity lemmas must be applied at the WHOLE application, which is
    /// the form `rigid_app_head` supports directly — the point of restating the
    /// premise over the preserved predicate.
    #[test]
    fn test_rigid_app_inv_applies_immunity_at_the_application() {
        let arms = Specification::rigid_app_inv_arms();
        for immune in [
            "rigid_app_iota_immune env (KExpr.app f a) hr",
            "rigid_app_delta_immune env (KExpr.app f a) hr",
        ] {
            assert!(arms.contains(immune), "missing or misapplied: {immune}");
        }
    }

    /// Free-variable check.
    #[test]
    fn test_rigid_app_inv_arms_reference_only_bound_hypotheses() {
        let arms = Specification::rigid_app_inv_arms();
        let chars: Vec<char> = arms.chars().collect();
        let mut bound: Vec<String> = Vec::new();
        for (idx, ch) in chars.iter().enumerate() {
            if *ch != '(' {
                continue;
            }
            let mut name = String::new();
            let mut cursor = idx + 1;
            while cursor < chars.len() && (chars[cursor].is_alphanumeric() || chars[cursor] == '_')
            {
                name.push(chars[cursor]);
                cursor += 1;
            }
            if !name.is_empty()
                && chars.get(cursor) == Some(&' ')
                && chars.get(cursor + 1) == Some(&':')
            {
                bound.push(name);
            }
        }
        let mut token = String::new();
        let mut referenced: Vec<String> = Vec::new();
        for ch in arms.chars() {
            if ch.is_alphanumeric() || ch == '_' || ch == '.' {
                token.push(ch);
            } else if !token.is_empty() {
                referenced.push(std::mem::take(&mut token));
            }
        }
        if !token.is_empty() {
            referenced.push(token);
        }
        for tok in referenced {
            let looks_local = tok.len() > 1
                && tok.starts_with('h')
                && tok
                    .chars()
                    .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
            if looks_local {
                assert!(
                    bound.contains(&tok),
                    "arm body references `{tok}`, which no binder in the same term introduces"
                );
            }
        }
    }

    #[test]
    fn test_rigid_app_inv_arms_parens_balanced() {
        let arms = Specification::rigid_app_inv_arms();
        let mut depth: i64 = 0;
        for ch in arms.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open");
        }
        assert_eq!(depth, 0);
    }
}
