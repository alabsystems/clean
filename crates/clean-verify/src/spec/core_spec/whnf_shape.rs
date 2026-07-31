// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What a weak head normal form cannot be.
//!
//! The completeness capstone case-splits on the shapes of the two normal forms
//! it compares. Two of the nine `KExpr` constructors can never appear there —
//! a `let_` always ζ-fires, and an application whose head is a `lam` always
//! β-fires — and the capstone needs those cases discharged rather than
//! reasoned about.
//!
//! ## Why this avoids `whnf_fuel_red_classifies`
//!
//! The obvious route to "which shape is this normal form" is
//! `whnf_fuel_red_classifies` (`whnf_progress.rs:2109`), which yields a
//! `whnf_noredex_class`. But it carries three side conditions —
//! `red_env_good the_red_env`, `red_closed_at e Nat.zero`, and
//! `consts_defined_red the_red_env e` — and each would have to be threaded into
//! the capstone's statement, where the closedness and constant-definedness
//! premises are genuine restrictions on the terms being compared.
//!
//! `whnf_fuel_red_no_redex` (`whnf_progress.rs:695`) is **unconditional**: a
//! successful loop result has no executable step, full stop. That single fact
//! suffices for the two impossible shapes, because `reduce_once_red` *computes*
//! on them: on `let_ ty v b` it returns `some (instantiate b v)`, and on
//! `app (lam A bd) arg` it returns `some (instantiate bd arg)`. Both contradict
//! `none` immediately.
//!
//! So the capstone rules these shapes out with no hypotheses beyond the ones it
//! already has. That is worth a separate brick: a completeness theorem carrying
//! an unnecessary closedness premise is materially weaker than it looks, and
//! the premise is easy to mistake for harmless.
//!
//! Both universe variants of each eliminator are provided, per the discipline
//! established in `kexpr_discr.rs` — the capstone's goals are `Type`-valued
//! witnesses, while its intermediate equational goals are `Prop`.
//!
//! `DerivedProved` throughout, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// An always-reducible shape: `(let_-or-beta label, payload binders, the form,
/// its reduct, the computation lemma name)`.
struct Reducible {
    label: &'static str,
    binders: &'static str,
    args: &'static str,
    form: &'static str,
    reduct: &'static str,
    computation: &'static str,
    prose: &'static str,
}

const REDUCIBLE: [Reducible; 2] = [
    Reducible {
        label: "let",
        binders: "(lty : KExpr) (lv : KExpr) (lb : KExpr)",
        args: "lty lv lb",
        form: "(KExpr.let_ lty lv lb)",
        reduct: "(instantiate lb lv)",
        computation: "reduce_once_red_let",
        prose: "let_",
    },
    Reducible {
        label: "beta",
        binders: "(bty : KExpr) (bbody : KExpr) (barg : KExpr)",
        args: "bty bbody barg",
        form: "(KExpr.app (KExpr.lam bty bbody) barg)",
        reduct: "(instantiate bbody barg)",
        computation: "reduce_once_red_beta",
        prose: "application whose head is a lambda",
    },
];

impl Specification {
    /// The two shapes a weak head normal form cannot have.
    pub(super) fn add_whnf_shape(&mut self) -> Result<(), SpecError> {
        for (src, description) in Self::whnf_shape_decls() {
            self.add_recursive_def(&src, &description)?;
        }
        Ok(())
    }

    /// Every declaration this module registers, as `(source, description)`.
    ///
    /// Generated rather than written inline so the shape tests can inspect the
    /// PROOF TERMS. The first version of the side-condition test scanned the
    /// file text and failed against its own description strings, which mention
    /// the premises precisely in order to say they are avoided — prose is not a
    /// dependency.
    fn whnf_shape_decls() -> Vec<(String, String)> {
        let mut out = Vec::new();

        // 1. The computations. Environment-free: β and ζ are pure syntactic
        //    rules, so `renv` is a parameter that never gets consulted.
        for r in &REDUCIBLE {
            out.push((
                format!(
                    "def {c} (renv : RedEnv) {binders} : \
                     Eq (OptionType KExpr) (reduce_once_red renv {form}) \
                     (OptionType.some KExpr {reduct}) := \
                     Eq.refl (OptionType KExpr) (reduce_once_red renv {form})",
                    c = r.computation,
                    binders = r.binders,
                    form = r.form,
                    reduct = r.reduct,
                ),
                format!(
                    "{c}: the executable step ALWAYS fires on a {prose} (Eq.refl, definitional). \
                     Environment-free — the RedEnv parameter is never consulted, because this \
                     rule is purely syntactic. DerivedProved, zero axiom_deps.",
                    c = r.computation,
                    prose = r.prose,
                ),
            ));
        }

        // 2. Hence the no-redex property is absurd on them, in both universes.
        for r in &REDUCIBLE {
            for (suffix, univ, elim) in [
                ("t", "Type", "opt_none_ne_some_t"),
                ("p", "Prop", "option_none_ne_some"),
            ] {
                out.push((
                    format!(
                        "def no_redex_not_{label}_{suffix} (C : {univ}) {binders} \
                         (h : Eq (OptionType KExpr) (reduce_once_red the_red_env {form}) \
                         (OptionType.none KExpr)) : C := \
                         {elim} KExpr {reduct} C \
                         (Eq.trans (OptionType KExpr) (OptionType.none KExpr) \
                         (reduce_once_red the_red_env {form}) \
                         (OptionType.some KExpr {reduct}) \
                         (Eq.symm (OptionType KExpr) (reduce_once_red the_red_env {form}) \
                         (OptionType.none KExpr) h) ({c} the_red_env {args}))",
                        label = r.label,
                        binders = r.binders,
                        form = r.form,
                        reduct = r.reduct,
                        c = r.computation,
                        args = r.args,
                    ),
                    format!(
                        "no_redex_not_{label}_{suffix}: a {prose} is NEVER a weak head normal \
                         form, so the no-redex property of a loop result is absurd there. \
                         Discharges into {univ}. DerivedProved, zero axiom_deps.",
                        label = r.label,
                        prose = r.prose,
                    ),
                ));
            }
        }

        // 3. The form the capstone applies: straight from a loop result,
        //    through the UNCONDITIONAL no-redex fact.
        for r in &REDUCIBLE {
            out.push((
                format!(
                    "def whnf_result_not_{label}_t (C : Type) (n : Nat) (e : KExpr) {binders} \
                     (h : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n e) \
                     (OptionType.some KExpr {form})) : C := \
                     no_redex_not_{label}_t C {args} \
                     (whnf_fuel_red_no_redex the_red_env n e {form} h)",
                    label = r.label,
                    binders = r.binders,
                    form = r.form,
                    args = r.args,
                ),
                format!(
                    "whnf_result_not_{label}_t: the executable whnf loop never RETURNS a {prose}. \
                     Composes whnf_fuel_red_no_redex — which is UNCONDITIONAL, needing no \
                     environment, closedness or constant-definedness side conditions — with the \
                     corresponding always-reducible fact. This is what the completeness capstone \
                     applies when it case-splits on the shape of a normal form, and routing it \
                     this way rather than through whnf_fuel_red_classifies is what keeps those \
                     three premises out of the capstone's statement. DerivedProved, zero \
                     axiom_deps.",
                    label = r.label,
                    prose = r.prose,
                ),
            ));
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The exclusions must NOT depend on the three side conditions that
    /// `whnf_fuel_red_classifies` carries. If any appeared in a PROOF TERM the
    /// capstone would inherit a closedness or environment premise, and a
    /// completeness theorem with an unnecessary closedness premise is a
    /// materially weaker statement than it looks.
    #[test]
    fn test_whnf_shape_terms_carry_no_side_conditions() {
        for (src, _) in Specification::whnf_shape_decls() {
            for premise in ["red_env_good", "red_closed_at", "consts_defined_red"] {
                assert!(
                    !src.contains(premise),
                    "generated term must not depend on {premise} — routing through the \
                     unconditional whnf_fuel_red_no_redex is the whole point.\nterm: {src}"
                );
            }
        }
    }

    /// Both loop-level exclusions must route through the unconditional fact.
    #[test]
    fn test_whnf_shape_routes_through_the_unconditional_no_redex() {
        let decls = Specification::whnf_shape_decls();
        let loop_level: Vec<&(String, String)> = decls
            .iter()
            .filter(|(s, _)| s.contains("def whnf_result_not_"))
            .collect();
        assert_eq!(
            loop_level.len(),
            2,
            "two loop-level exclusions: let_ and beta"
        );
        for (src, _) in loop_level {
            assert!(
                src.contains("whnf_fuel_red_no_redex the_red_env n e"),
                "loop-level exclusion must go through whnf_fuel_red_no_redex"
            );
        }
    }

    /// Both universe variants exist for each shape — the capstone's goals are
    /// `Type`-valued witnesses, its intermediate goals `Prop`.
    #[test]
    fn test_whnf_shape_provides_both_universe_variants() {
        let names: Vec<String> = Specification::whnf_shape_decls()
            .into_iter()
            .map(|(s, _)| s.split_whitespace().nth(1).unwrap_or("").to_string())
            .collect();
        for expected in [
            "reduce_once_red_let",
            "reduce_once_red_beta",
            "no_redex_not_let_t",
            "no_redex_not_let_p",
            "no_redex_not_beta_t",
            "no_redex_not_beta_p",
            "whnf_result_not_let_t",
            "whnf_result_not_beta_t",
        ] {
            assert!(
                names.iter().any(|n| n == expected),
                "missing declaration: {expected} (have {names:?})"
            );
        }
        assert_eq!(names.len(), 8, "expected exactly 8 declarations");
    }

    /// The `Prop` variant must use the `Prop` no-confusion and the `Type`
    /// variant the `Type` one — mixing them is a universe conflict that only a
    /// full spec build would surface.
    #[test]
    fn test_whnf_shape_universe_variants_use_matching_eliminators() {
        for (src, _) in Specification::whnf_shape_decls() {
            if src.contains("(C : Prop)") {
                assert!(
                    src.contains("option_none_ne_some KExpr"),
                    "a Prop-valued exclusion must use the Prop no-confusion"
                );
                assert!(!src.contains("opt_none_ne_some_t"));
            }
            if src.contains("(C : Type)") && src.contains("no_redex_not_") && src.contains(":= opt")
            {
                assert!(
                    src.contains("opt_none_ne_some_t KExpr"),
                    "a Type-valued exclusion must use the Type no-confusion"
                );
            }
        }
    }

    #[test]
    fn test_whnf_shape_terms_parens_balanced() {
        for (src, _) in Specification::whnf_shape_decls() {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "close paren before its open in: {src}");
            }
            assert_eq!(depth, 0, "unbalanced: {src}");
        }
    }
}
