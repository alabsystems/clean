// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Head rigidity for applications on a **stuck** head.
//!
//! ## Why the existing neutral-app inversion does not cover this
//!
//! `par_reduces_cd_star_neutral_app_inv_eq` (`wall_a_completeness.rs:1912`)
//! looks like the lemma for application heads, but its premise is
//! `iota_neutral f`, and `iota_neutral` (`wall_a_completeness.rs:325-329`) has
//! exactly **two** constructors:
//!
//! * `const n us`, requiring `const_whnf n us` **and** that the constant is
//!   δ-dead, and
//! * `app f a`, requiring `iota_neutral f` recursively.
//!
//! There is no `sort`, `pi`, `proj` or `lit` arm. So `iota_neutral` describes
//! *constant-headed* spines only, and the `stuck` arm of `whnf_noredex_class`
//! — an application whose head is `whnf_stuck_head`, i.e. a sort, pi, literal
//! or projection — is **not covered by any inversion in the tree**.
//!
//! That is a real hole on the capstone's path, not a stylistic one: the
//! reflected calculus is untyped, so `app (sort u) a` is a perfectly good
//! syntactic normal form and the completeness recursion can meet it.
//!
//! ## Why it is nonetheless easy now
//!
//! With `stuck_immunity.rs` landed, every non-congruence way out of
//! `app f a` is closed:
//!
//! | `par_reduces_cd` arm | why it cannot apply |
//! |---|---|
//! | `beta` | the head would have to be a `lam`, and `whnf_stuck_head` has no `lam` arm |
//! | `iota` / `delta` | `whnf_stuck_app_iota_immune` / `_delta_immune` — the head carries no constant name |
//! | `lam` `pi` `forall_` `let_` `let_cong` `proj` | conclude at a different head constructor |
//! | `refl`, `app` | the two survivors |
//!
//! So the shape is exactly the one `proj_rigidity.rs` already used, and the
//! new ingredient is `whnf_stuck_head_not_lam`, which is again an argument from
//! an **absent** constructor.
//!
//! ## What is deliberately NOT here: the multi-step version
//!
//! Lifting this to `par_reduces_cd_star` needs the head to still be stuck
//! after reducing — `whnf_stuck_head f -> par_reduces_cd env f f2 ->
//! whnf_stuck_head f2` — and that preservation lemma is genuinely separate
//! work, because its own `app` case wants an application inversion. The
//! non-circular order is: prove preservation by induction on
//! `whnf_stuck_head`, using the SINGLE-STEP inversion below (which needs no
//! preservation), and only then lift to the closure. A first draft of this
//! module skipped that and wrote a star version referencing a
//! `stuck_head_par_star_preserved` that does not exist; it is dropped rather
//! than shipped dangling.
//!
//! `DerivedProved` throughout, empty axiom closures; the witness is
//! census-neutral.

use crate::spec::core_spec::kexpr_discr::CD_STRUCTURAL_ARMS;
use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `CD_STRUCTURAL_ARMS` indices that are *not* the general `app` congruence.
/// Index 0 is `beta` (handled specially — it needs the not-a-lambda argument)
/// and index 1 is `app` itself, the substantive case.
const BETA_INDEX: usize = 0;
const APP_INDEX: usize = 1;

impl Specification {
    /// Stuck-headed applications reduce only to stuck-headed applications.
    pub(super) fn add_stuck_app_rigidity(&mut self) -> Result<(), SpecError> {
        self.add_stuck_head_not_lam()?;
        self.add_stuck_app_witness()?;
        self.add_stuck_app_inv_step()?;
        Ok(())
    }

    /// A stuck head is never a lambda — another argument from an absent arm.
    fn add_stuck_head_not_lam(&mut self) -> Result<(), SpecError> {
        // One arm per whnf_stuck_head constructor; each concludes at a head
        // that is not `lam`, so kexpr_discr_t kills the equation. `app` and
        // `proj` recurse and therefore carry induction hypotheses; `projw`'s
        // premise is an `is_whnf`, not a recursive occurrence, so it does not.
        let goal = "(C : Type)";
        let motive = "forall (C : Type) (lty : KExpr) (lbd : KExpr), \
                      Eq KExpr x (KExpr.lam lty lbd) -> C";
        let motive_at = |v: &str| {
            format!(
                "forall (C : Type) (lty : KExpr) (lbd : KExpr), \
                 Eq KExpr {v} (KExpr.lam lty lbd) -> C"
            )
        };
        let kill = |form: &str| {
            format!(
                "(fun (C : Type) (lty : KExpr) (lbd : KExpr) \
                 (heq : Eq KExpr {form} (KExpr.lam lty lbd)) => \
                 kexpr_discr_t C {form} (KExpr.lam lty lbd) heq (Eq.refl Bool Bool.false)) "
            )
        };

        let mut arms = String::new();
        arms.push_str(&format!("(fun (n : Level) => {})", kill("(KExpr.sort n)")));
        arms.push(' ');
        arms.push_str(&format!(
            "(fun (pty : KExpr) (pbody : KExpr) => {})",
            kill("(KExpr.pi pty pbody)")
        ));
        arms.push(' ');
        arms.push_str(&format!(
            "(fun (af : KExpr) (aa : KExpr) (_hf : whnf_stuck_head af) (_ih : {ih}) => {k})",
            ih = motive_at("af"),
            k = kill("(KExpr.app af aa)")
        ));
        arms.push(' ');
        arms.push_str(&format!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (_hsub : whnf_stuck_head sub) \
             (_ih : {ih}) => {k})",
            ih = motive_at("sub"),
            k = kill("(KExpr.proj s i sub)")
        ));
        arms.push(' ');
        arms.push_str(&format!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (_hw : is_whnf sub) => {k})",
            k = kill("(KExpr.proj s i sub)")
        ));
        arms.push(' ');
        arms.push_str(&format!("(fun (v : Nat) => {})", kill("(KExpr.lit v)")));

        self.add_recursive_def(
            &format!(
                "def whnf_stuck_head_not_lam (f : KExpr) (hs : whnf_stuck_head f) : \
                 forall {goal} (lty : KExpr) (lbd : KExpr), \
                 Eq KExpr f (KExpr.lam lty lbd) -> C := \
                 whnf_stuck_head.rec (fun (x : KExpr) (_h : whnf_stuck_head x) => {motive}) \
                 {arms} f hs"
            ),
            "whnf_stuck_head_not_lam: a stuck head is never a lambda. Like \
             whnf_stuck_head_no_const, this is an argument from an ABSENT constructor — \
             whnf_stuck_head has no lam arm — so every one of its six arms concludes at a \
             different head and dies by generic discrimination. It is what rules out the beta \
             case when inverting reduction out of a stuck-headed application. DerivedProved, \
             zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_stuck_app_witness(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive StuckAppRedWitness (env : RedEnv) (f : KExpr) (a : KExpr) (t : KExpr) : \
             Type\n\
             | mk : forall (f2 : KExpr) (a2 : KExpr), Eq KExpr t (KExpr.app f2 a2) -> \
             par_reduces_cd_star env f f2 -> par_reduces_cd_star env a a2 -> \
             StuckAppRedWitness env f a t",
            "StuckAppRedWitness env f a t: t IS an application, and both its function and its \
             argument are reachable from the originals. The conclusion of head rigidity for \
             stuck-headed applications; a single-constructor witness because the spec has no \
             Exists. Census-neutral.",
        )?;
        Ok(())
    }

    /// The eleven minor premises, in `par_reduces_cd` declaration order.
    fn stuck_app_arms() -> String {
        let goal = |t: &str| format!("(StuckAppRedWitness env f a {t})");
        let motive_at = |p: &str, q: &str| {
            format!(
                "forall (f : KExpr) (a : KExpr), whnf_stuck_head f -> \
                 Eq KExpr {p} (KExpr.app f a) -> {g}",
                g = goal(q)
            )
        };

        // refl: nothing moved.
        let mut arms = format!(
            "(fun (e0 : KExpr) (f : KExpr) (a : KExpr) (_hs : whnf_stuck_head f) \
             (heq : Eq KExpr e0 (KExpr.app f a)) => \
             StuckAppRedWitness.mk env f a e0 f a heq \
             (par_reduces_cd_star.refl env f) (par_reduces_cd_star.refl env a)) "
        );

        // `names` supplies a name for each recursive proof binder. Anonymous
        // `_` is right for the arms that discard them, but the substantive
        // `app` arm USES its two proofs, and a `_`-bound proof referenced by
        // name is an unknown-identifier error the kernel only reports after a
        // full spec build. Naming is therefore driven from the same table that
        // generates the binders.
        let binder_block = |idx: usize, names: &[&str]| {
            let (payload, pairs, _src, _tgt) = CD_STRUCTURAL_ARMS[idx];
            assert!(
                names.is_empty() || names.len() == pairs.len(),
                "arm {idx}: expected one name per recursive premise"
            );
            let mut proofs = String::new();
            let mut ihs = String::new();
            for (slot, (from, to)) in pairs.iter().enumerate() {
                let binder = names.get(slot).copied().unwrap_or("_");
                proofs.push_str(&format!("({binder} : par_reduces_cd env {from} {to}) "));
                ihs.push_str(&format!("(_ : {}) ", motive_at(from, to)));
            }
            (payload, proofs, ihs)
        };

        // beta: the head would have to be a lambda, which a stuck head is not.
        {
            let (payload, proofs, ihs) = binder_block(BETA_INDEX, &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[BETA_INDEX];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(f : KExpr) (a : KExpr) \
                 (hs : whnf_stuck_head f) (heq : Eq KExpr {src} (KExpr.app f a)) => \
                 whnf_stuck_head_not_lam f hs {g} bA bbody \
                 (Eq.symm KExpr (KExpr.lam bA bbody) f \
                 (app_inj_fst (KExpr.lam bA bbody) barg f a heq))) ",
                g = goal(tgt)
            ));
        }

        // app: THE substantive congruence arm.
        {
            let (payload, proofs, ihs) = binder_block(APP_INDEX, &["hpf", "hpa"]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[APP_INDEX];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(f : KExpr) (a : KExpr) \
                 (_hs : whnf_stuck_head f) (heq : Eq KExpr {src} (KExpr.app f a)) => \
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

        // lam, pi, forall_, let_ : conclude at a different head.
        for idx in 2..6 {
            let (payload, proofs, ihs) = binder_block(idx, &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[idx];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(f : KExpr) (a : KExpr) \
                 (_hs : whnf_stuck_head f) (heq : Eq KExpr {src} (KExpr.app f a)) => \
                 kexpr_discr_t {g} {src} (KExpr.app f a) heq (Eq.refl Bool Bool.false)) ",
                g = goal(tgt)
            ));
        }

        // iota / delta: closed by the stuck-spine immunity lemmas.
        for (ctor, envsel, immune, var) in [
            ("iota", "red_rec env", "whnf_stuck_app_iota_immune", "ie"),
            ("delta", "red_def env", "whnf_stuck_app_delta_immune", "de"),
        ] {
            arms.push_str(&format!(
                "(fun ({var} : KExpr) ({var}2 : KExpr) \
                 (hst : {ctor}_step ({envsel}) {var} {var}2) (f : KExpr) (a : KExpr) \
                 (hs : whnf_stuck_head f) (heq : Eq KExpr {var} (KExpr.app f a)) => \
                 opt_none_ne_some_t KExpr {var}2 {g} \
                 (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
                 ({ctor}_reduct ({envsel}) (KExpr.app f a)) \
                 (OptionType.some KExpr {var}2) \
                 (Eq.symm (OptionType KExpr) ({ctor}_reduct ({envsel}) (KExpr.app f a)) \
                 (OptionType.none KExpr) ({immune} env f a hs)) \
                 (Eq.substType KExpr \
                 (fun (z : KExpr) => Eq (OptionType KExpr) ({ctor}_reduct ({envsel}) z) \
                 (OptionType.some KExpr {var}2)) {var} (KExpr.app f a) heq hst))) ",
                g = goal(&format!("{var}2"))
            ));
        }

        // let_cong, proj: different heads again.
        for idx in [6usize, 7usize] {
            let (payload, proofs, ihs) = binder_block(idx, &[]);
            let (_, _, src, tgt) = CD_STRUCTURAL_ARMS[idx];
            arms.push_str(&format!(
                "(fun {payload} {proofs}{ihs}(f : KExpr) (a : KExpr) \
                 (_hs : whnf_stuck_head f) (heq : Eq KExpr {src} (KExpr.app f a)) => \
                 kexpr_discr_t {g} {src} (KExpr.app f a) heq (Eq.refl Bool Bool.false)) ",
                g = goal(tgt)
            ));
        }

        arms
    }

    fn add_stuck_app_inv_step(&mut self) -> Result<(), SpecError> {
        let arms = Self::stuck_app_arms();
        self.add_recursive_def(
            &format!(
                "def par_reduces_cd_stuck_app_inv (env : RedEnv) (p : KExpr) (q : KExpr) \
                 (h : par_reduces_cd env p q) : \
                 forall (f : KExpr) (a : KExpr), whnf_stuck_head f -> \
                 Eq KExpr p (KExpr.app f a) -> StuckAppRedWitness env f a q := \
                 par_reduces_cd.rec env \
                 (fun (pp : KExpr) (qq : KExpr) (_h : par_reduces_cd env pp qq) => \
                 forall (f : KExpr) (a : KExpr), whnf_stuck_head f -> \
                 Eq KExpr pp (KExpr.app f a) -> StuckAppRedWitness env f a qq) \
                 {arms}p q h"
            ),
            "par_reduces_cd_stuck_app_inv: SINGLE-STEP head rigidity for an application on a \
             STUCK head. Fills a genuine hole: the existing neutral-app inversion requires \
             iota_neutral, which has only const and app arms, so it describes constant-headed \
             spines only and says nothing about an application headed by a sort, pi, literal or \
             projection — shapes the untyped reflected calculus admits as normal forms. Every \
             escape is closed: beta by whnf_stuck_head_not_lam, iota and delta by the \
             stuck-spine immunity lemmas, the remaining structural arms by head discrimination. \
             refl and the app congruence survive. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stuck_app_arms_has_eleven_minor_premises() {
        let arms = Specification::stuck_app_arms();
        let minors = arms.matches("(fun ").count()
            - arms.matches("(fun (z : KExpr)").count()
            - arms.matches("(fun (hf :").count();
        assert_eq!(minors, 11, "expected 11 minor premises, got {minors}");
    }

    /// Declaration order, with `iota`/`delta` at positions 8 and 9.
    #[test]
    fn test_stuck_app_arms_declaration_order() {
        let arms = Specification::stuck_app_arms();
        let landmarks = [
            "(fun (e0 : KExpr)",
            "whnf_stuck_head_not_lam",
            "app_inj_snd",
            "(KExpr.lam lty lbody)",
            "(KExpr.pi pdom pbody)",
            "(KExpr.forall_ qdom qbody)",
            "(KExpr.let_ zty zval zbody)",
            "whnf_stuck_app_iota_immune",
            "whnf_stuck_app_delta_immune",
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

    /// Every recursive premise gets both a proof and an IH binder.
    #[test]
    fn test_stuck_app_arms_binds_an_ih_per_recursive_premise() {
        let arms = Specification::stuck_app_arms();
        // Count proof binders whatever they are NAMED: the substantive app arm
        // binds its two by name (hpf / hpa) because it uses them, the rest are
        // anonymous. Counting only `_` here silently under-counted by two.
        let proofs = arms.matches(" : par_reduces_cd env ").count()
            - arms.matches("(_hs : par_reduces_cd env ").count();
        let ihs = arms
            .matches("(_ : forall (f : KExpr) (a : KExpr), whnf_stuck_head f")
            .count();
        assert_eq!(
            proofs, 18,
            "18 recursive premises across the eight structural arms"
        );
        assert_eq!(ihs, 18, "one induction hypothesis each");
    }

    /// The two escapes this module exists to close must actually be used.
    #[test]
    fn test_stuck_app_arms_close_beta_and_the_step_arms() {
        let arms = Specification::stuck_app_arms();
        assert!(
            arms.contains("whnf_stuck_head_not_lam f hs"),
            "the beta arm must be killed by the not-a-lambda argument"
        );
        for immune in [
            "whnf_stuck_app_iota_immune env f a hs",
            "whnf_stuck_app_delta_immune env f a hs",
        ] {
            assert!(
                arms.contains(immune),
                "missing immunity application: {immune}"
            );
        }
    }

    /// THE REGRESSION GUARD FOR THIS ROUND. Every hypothesis-shaped identifier
    /// used in an arm body must actually be bound by that arm.
    ///
    /// The first version generated ALL recursive proof binders as anonymous
    /// `_` and then referenced two of them by name in the substantive `app`
    /// arm. That is an unknown-identifier error the kernel reports only after a
    /// full ~21-minute spec build, and no count, order or balance check can see
    /// it: the term is perfectly well-shaped, it just mentions a name nothing
    /// binds.
    ///
    /// Sound for this module because every global it references
    /// (`whnf_*`, `kexpr_*`, `app_inj_*`, `opt_*`, `par_*`, `Eq.*`,
    /// `StuckAppRedWitness*`) fails the `h[a-z0-9_]*` shape.
    #[test]
    fn test_stuck_app_arms_reference_only_bound_hypotheses() {
        let arms = Specification::stuck_app_arms();

        let mut bound: Vec<String> = Vec::new();
        let bytes: Vec<char> = arms.chars().collect();
        for (idx, ch) in bytes.iter().enumerate() {
            if *ch != '(' {
                continue;
            }
            let mut name = String::new();
            let mut cursor = idx + 1;
            while cursor < bytes.len() && (bytes[cursor].is_alphanumeric() || bytes[cursor] == '_')
            {
                name.push(bytes[cursor]);
                cursor += 1;
            }
            // A binder looks like `(name : ...`.
            if !name.is_empty()
                && bytes.get(cursor) == Some(&' ')
                && bytes.get(cursor + 1) == Some(&':')
            {
                bound.push(name);
            }
        }

        let mut referenced: Vec<String> = Vec::new();
        let mut token = String::new();
        for ch in arms.chars() {
            if ch.is_alphanumeric() || ch == '_' || ch == '.' {
                token.push(ch);
            } else {
                if !token.is_empty() {
                    referenced.push(std::mem::take(&mut token));
                } else {
                    token.clear();
                }
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
                    "arm body references `{tok}`, which no binder in the same term introduces — \
                     an unknown-identifier error the kernel only reports after a full spec build"
                );
            }
        }
    }

    #[test]
    fn test_stuck_app_arms_parens_balanced() {
        let arms = Specification::stuck_app_arms();
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
