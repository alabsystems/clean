// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reduction out of a rigid-headed term preserves the head **tag**.
//!
//! ```text
//! rigid_app_head_star_preserves_tag :
//!   rigid_app_head e -> par_reduces_cd_star env e w -> Eq Nat (kexpr_tag e) (kexpr_tag w)
//! ```
//!
//! ## Why a tag, and why this is the whole point
//!
//! The completeness capstone must conclude that two normal forms with a common
//! reduct have the **same head**. The obvious route is a grid over pairs of
//! heads — 7 diagonal cases plus 42 cross-head absurdities, a term at
//! `def_eq_struct` scale. Factoring through `kexpr_tag` collapses that: prove
//! the one-sided fact above, and the two sides meet in a single `Eq.trans`
//! through the common reduct:
//!
//! ```text
//! kexpr_tag na = kexpr_tag w = kexpr_tag nb
//! ```
//!
//! Eight cases instead of sixty-four, and the cross-head contradictions
//! disappear entirely — they become one tag equation, with `kexpr_discr` doing
//! the rest.
//!
//! ## The six arms
//!
//! Every arm applies the star inversion for its head shape and then transports
//! the tag. Five of the six inversions were already in tree or landed in this
//! program; the fifth — for applications — is the one whose multi-step version
//! needed `rigid_app_head` to exist at all.
//!
//! | arm | inversion | note |
//! |---|---|---|
//! | `sort` | `par_reduces_cd_star_sort_inv_eq` | equation form |
//! | `pi` | `par_reduces_cd_star_pi_inv_eq` | continuation form; its answer type is `C : Type`, so the `Eq` goal is wrapped in `LiftP` |
//! | `lit` | `par_reduces_cd_star_lit_inv_eq` | landed with the discrimination brick |
//! | `app` | `par_reduces_cd_star_rigid_app_inv` | needed the preserved predicate |
//! | `proj` | `par_reduces_cd_star_proj_inv` | landed with proj rigidity |
//!
//! In each case the two tags *compute* to the same numeral, so the closing step
//! is `Eq.refl` under a `kexpr_tag` congruence — the payoff of having made
//! `kexpr_tag` a computing function rather than a relation.
//!
//! ## Scope
//!
//! This covers the rigid heads: `sort`, `pi`, `lit`, application-on-rigid, and
//! `proj`. The two whnf shapes it does **not** cover are `lam` and a
//! `const`-headed neutral. `lam` needs only the binder inversion and is
//! mechanical; the `const` case genuinely needs δ-deadness, i.e.
//! `consts_defined_red`, exactly as recorded for classification. Neither is
//! papered over here.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Tag preservation for rigid heads.
    pub(super) fn add_rigid_tag(&mut self) -> Result<(), SpecError> {
        self.add_rigid_tag_preservation()?;
        Ok(())
    }

    /// The six minor premises of the tag-preservation induction.
    fn rigid_tag_arms() -> String {
        let motive_at = |x: &str| {
            format!(
                "forall (w : KExpr), par_reduces_cd_star env {x} w -> \
                 Eq Nat (kexpr_tag {x}) (kexpr_tag w)"
            )
        };
        // From `Eq KExpr w <form>` conclude `Eq Nat (kexpr_tag <form>) (kexpr_tag w)`.
        let via_equation = |form: &str, proof: &str| {
            format!(
                "Eq.symm Nat (kexpr_tag w) (kexpr_tag {form}) \
                 (Eq.cong KExpr Nat kexpr_tag w {form} ({proof}))"
            )
        };

        let mut arms = String::new();

        // sort: the equation-form inversion.
        arms.push_str(&format!(
            "(fun (n : Level) (w : KExpr) \
             (hs : par_reduces_cd_star env (KExpr.sort n) w) => {body}) ",
            body = via_equation(
                "(KExpr.sort n)",
                "par_reduces_cd_star_sort_inv_eq env n w hs"
            )
        ));

        // pi: the continuation-form inversion. BOTH binder inversions take
        // their answer type as `C : Type` (the `_eq` variant too —
        // par_reduces_cd_injectivity.rs:264), and the goal here is an `Eq`,
        // which is Prop-valued. Passing it directly is a universe conflict, not
        // a coercion. So the answer is wrapped in `LiftP` — the spec's
        // Prop-into-Type lift (`whnf_progress.rs:4745`) — and unwrapped
        // immediately by `LiftP.rec`.
        //
        // The sort and lit arms are unaffected: their inversions are in
        // EQUATION form and return an `Eq KExpr` outright, with no answer-type
        // parameter to mis-instantiate.
        {
            let tag_eq = "Eq Nat (kexpr_tag (KExpr.pi pty pbody)) (kexpr_tag w)";
            arms.push_str(&format!(
                "(fun (pty : KExpr) (pbody : KExpr) (w : KExpr) \
                 (hs : par_reduces_cd_star env (KExpr.pi pty pbody) w) => \
                 LiftP.rec ({tag_eq}) \
                 (fun (_l : LiftP ({tag_eq})) => {tag_eq}) \
                 (fun (p : {tag_eq}) => p) \
                 (par_reduces_cd_star_pi_inv_eq env pty pbody w (LiftP ({tag_eq})) hs \
                 (fun (dom2 : KExpr) (body2 : KExpr) \
                 (heq : Eq KExpr w (KExpr.pi dom2 body2)) \
                 (_h1 : par_reduces_cd_star env pty dom2) \
                 (_h2 : par_reduces_cd_star env pbody body2) => \
                 LiftP.up ({tag_eq}) \
                 (Eq.symm Nat (kexpr_tag w) (kexpr_tag (KExpr.pi dom2 body2)) \
                 (Eq.cong KExpr Nat kexpr_tag w (KExpr.pi dom2 body2) heq))))) "
            ));
        }

        // lit
        arms.push_str(&format!(
            "(fun (v : Nat) (w : KExpr) \
             (hs : par_reduces_cd_star env (KExpr.lit v) w) => {body}) ",
            body = via_equation("(KExpr.lit v)", "par_reduces_cd_star_lit_inv_eq env v w hs")
        ));

        // app: unpack the witness, then transport.
        arms.push_str(&format!(
            "(fun (af : KExpr) (aa : KExpr) (hraf : rigid_app_head af) \
             (_ih : {ih}) (w : KExpr) \
             (hs : par_reduces_cd_star env (KExpr.app af aa) w) => \
             StuckAppRedWitness.rec env af aa w \
             (fun (_x : StuckAppRedWitness env af aa w) => \
             Eq Nat (kexpr_tag (KExpr.app af aa)) (kexpr_tag w)) \
             (fun (f2 : KExpr) (a2 : KExpr) (heq : Eq KExpr w (KExpr.app f2 a2)) \
             (_r1 : par_reduces_cd_star env af f2) \
             (_r2 : par_reduces_cd_star env aa a2) => {body}) \
             (par_reduces_cd_star_rigid_app_inv env (KExpr.app af aa) w hs af aa \
             (rigid_app_head.app af aa hraf) (Eq.refl KExpr (KExpr.app af aa)))) ",
            ih = motive_at("af"),
            body = via_equation("(KExpr.app f2 a2)", "heq")
        ));

        // proj
        arms.push_str(&format!(
            "(fun (s : Name) (i : Nat) (sub : KExpr) (w : KExpr) \
             (hs : par_reduces_cd_star env (KExpr.proj s i sub) w) => \
             ProjRedWitness.rec env s i sub w \
             (fun (_x : ProjRedWitness env s i sub w) => \
             Eq Nat (kexpr_tag (KExpr.proj s i sub)) (kexpr_tag w)) \
             (fun (sub2 : KExpr) (heq : Eq KExpr w (KExpr.proj s i sub2)) \
             (_r : par_reduces_cd_star env sub sub2) => {body}) \
             (par_reduces_cd_star_proj_inv env (KExpr.proj s i sub) w hs s i sub \
             (Eq.refl KExpr (KExpr.proj s i sub)))) ",
            body = via_equation("(KExpr.proj s i sub2)", "heq")
        ));

        // bvar: LAST, matching the constructor order. Like `lit` and unlike
        // `pi`, its inversion is in EQUATION form and returns an `Eq KExpr`
        // outright, so no `LiftP` wrap is needed.
        arms.push_str(&format!(
            "(fun (i : Nat) (w : KExpr) \
             (hs : par_reduces_cd_star env (KExpr.bvar i) w) => {body}) ",
            body = via_equation(
                "(KExpr.bvar i)",
                "par_reduces_cd_star_bvar_inv_eq env i w hs"
            )
        ));

        arms
    }

    fn add_rigid_tag_preservation(&mut self) -> Result<(), SpecError> {
        let arms = Self::rigid_tag_arms();
        self.add_recursive_def(
            &format!(
                "def rigid_app_head_star_preserves_tag (env : RedEnv) (e : KExpr) \
                 (hr : rigid_app_head e) : \
                 forall (w : KExpr), par_reduces_cd_star env e w -> \
                 Eq Nat (kexpr_tag e) (kexpr_tag w) := \
                 rigid_app_head.rec \
                 (fun (x : KExpr) (_h : rigid_app_head x) => \
                 forall (w : KExpr), par_reduces_cd_star env x w -> \
                 Eq Nat (kexpr_tag x) (kexpr_tag w)) \
                 {arms}e hr"
            ),
            "rigid_app_head_star_preserves_tag: reduction out of a rigid-headed term preserves \
             the HEAD TAG. This is the load-bearing shape of the completeness capstone's head \
             argument, and it is deliberately ONE-SIDED. Concluding that two normal forms with a \
             common reduct share a head, by reasoning about PAIRS of heads, is a 7x7 grid — 7 \
             diagonal cases plus 42 cross-head absurdities, a term at def_eq_struct scale. \
             Factoring through kexpr_tag collapses it: the two sides meet in a single Eq.trans \
             through the common reduct, and the cross-head contradictions become one tag equation \
             for kexpr_discr to dispatch. Each of the six arms applies the star inversion for its \
             head shape and transports the tag; in every case the two tags COMPUTE to the same \
             numeral, so the closing step is Eq.refl under a kexpr_tag congruence — the payoff of \
             kexpr_tag being a computing function rather than a relation. SCOPE: covers the rigid \
             heads (sort, pi, lit, application-on-rigid, proj). Not covered: lam, which needs \
             only the binder inversion, and a const-headed neutral, which genuinely needs \
             delta-deadness (consts_defined_red). Neither is papered over. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Five arms, one per `rigid_app_head` constructor.
    ///
    /// Counted at paren-depth ZERO. Earlier revisions subtracted known inner
    /// lambdas by pattern, which broke the moment the `pi` arm gained a `LiftP`
    /// wrap with two more of them — a test that has to be edited whenever the
    /// proof changes internally is not guarding anything.
    #[test]
    fn test_rigid_tag_arms_has_six_minor_premises() {
        let arms = Specification::rigid_tag_arms();
        let chars: Vec<char> = arms.chars().collect();
        let mut depth: i64 = 0;
        let mut top_level_lambdas = 0usize;
        for (idx, ch) in chars.iter().enumerate() {
            match ch {
                '(' => {
                    if depth == 0 && arms[idx..].starts_with("(fun ") {
                        top_level_lambdas += 1;
                    }
                    depth += 1;
                }
                ')' => depth -= 1,
                _ => {}
            }
        }
        assert_eq!(
            top_level_lambdas, 6,
            "rigid_app_head has six constructors, so the recursor takes six minor premises; \
             found {top_level_lambdas} top-level lambdas"
        );
    }

    /// Declaration order of `rigid_app_head`: sort, pi, lit, app, proj, bvar.
    #[test]
    fn test_rigid_tag_arms_declaration_order() {
        let arms = Specification::rigid_tag_arms();
        let landmarks = [
            "par_reduces_cd_star_sort_inv_eq",
            "par_reduces_cd_star_pi_inv_eq env pty pbody",
            "par_reduces_cd_star_lit_inv_eq",
            "par_reduces_cd_star_rigid_app_inv",
            "par_reduces_cd_star_proj_inv",
            "par_reduces_cd_star_bvar_inv_eq",
        ];
        let mut cursor = 0usize;
        for (position, mark) in landmarks.iter().enumerate() {
            let found = arms[cursor..]
                .find(mark)
                .unwrap_or_else(|| panic!("arm {position} ({mark}) missing or out of order"));
            cursor += found + mark.len();
        }
    }

    /// Each arm must actually USE an inversion. An arm that closed by `Eq.refl`
    /// alone would be claiming the tag is preserved without inverting the
    /// reduction — true only because the inversion says so.
    #[test]
    fn test_every_arm_applies_an_inversion() {
        let arms = Specification::rigid_tag_arms();
        let inversions = [
            "par_reduces_cd_star_sort_inv_eq",
            "par_reduces_cd_star_pi_inv_eq",
            "par_reduces_cd_star_lit_inv_eq",
            "par_reduces_cd_star_rigid_app_inv",
            "par_reduces_cd_star_proj_inv",
        ];
        for inv in inversions {
            assert!(arms.contains(inv), "no arm applies {inv}");
        }
    }

    /// Only the `app` arm has a recursive premise, so exactly one IH binder.
    #[test]
    fn test_only_the_app_arm_binds_an_induction_hypothesis() {
        let arms = Specification::rigid_tag_arms();
        assert_eq!(
            arms.matches("(_ih : forall (w : KExpr)").count(),
            1,
            "rigid_app_head has exactly one recursive arm (app), hence one IH binder"
        );
        assert_eq!(
            arms.matches("(hraf : rigid_app_head af)").count(),
            1,
            "the app arm binds its recursive premise by name — it rebuilds rigid_app_head.app"
        );
    }

    /// Free-variable check.
    #[test]
    fn test_rigid_tag_arms_reference_only_bound_hypotheses() {
        let arms = Specification::rigid_tag_arms();
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
    fn test_rigid_tag_arms_parens_balanced() {
        let arms = Specification::rigid_tag_arms();
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
