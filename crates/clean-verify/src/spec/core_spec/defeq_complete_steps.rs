// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The completeness recursion's **per-head steps**.
//!
//! Each takes the component acceptances the recursion produced and returns an
//! acceptance for the composite:
//!
//! ```text
//! def_eq_complete_step_pi :
//!   whnf_fuel_red the_red_env n a = some (pi ty1 bd1)
//!     -> whnf_fuel_red the_red_env n b = some (pi ty2 bd2)
//!     -> DefEqFuelAccepts ty1 ty2 -> DefEqFuelAccepts bd1 bd2
//!     -> DefEqFuelAccepts a b
//! ```
//!
//! and likewise for `lam`, `app` and `proj`.
//!
//! ## The fuel mismatch these exist to resolve
//!
//! Three fuels arrive independent of one another: the whnf legs are at some `n`,
//! and each component acceptance hides its own. `def_eq_fuel_pi_cong` and its
//! siblings demand **one** fuel for all of them.
//!
//! So each step: pairs the component acceptances to a shared `k`
//! (`def_eq_fuel_accepts_pair`), then raises the legs from `n` and the
//! components from `k` to `n + k` — `whnf_fuel_red_le` on one side,
//! `def_eq_fuel_le` on the other — and applies the congruence there. The result
//! is an acceptance at `n + k + 1`, repackaged as a `DefEqFuelAccepts`.
//!
//! Doing this once per head, rather than inline in the capstone, is what keeps
//! the capstone's eight leaves to a few lines each. It also isolates the only
//! genuinely fiddly arithmetic in the whole development: three unrelated fuels
//! collapsing to one.
//!
//! ## What is deliberately absent
//!
//! These take the component acceptances as **hypotheses**. They are the
//! recursion's *steps*, not the recursion — the induction on
//! `rbelow_plus_acc` that produces those hypotheses is the capstone, and
//! assembling it here would be a masquerade.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `(head, congruence lemma, payload binders, na form, nb form, component
/// pairs)`. `let_` is absent on purpose — three components need a chained
/// pairing, and it is landed separately once this pattern is verified.
struct Step {
    head: &'static str,
    cong: &'static str,
    binders: &'static str,
    na: &'static str,
    nb: &'static str,
    /// Component pairs, as `(left, right)`.
    comps: &'static [(&'static str, &'static str)],
}

const STEPS: [Step; 4] = [
    Step {
        head: "pi",
        cong: "def_eq_fuel_pi_cong",
        binders: "(ty1 : KExpr) (bd1 : KExpr) (ty2 : KExpr) (bd2 : KExpr)",
        na: "(KExpr.pi ty1 bd1)",
        nb: "(KExpr.pi ty2 bd2)",
        comps: &[("ty1", "ty2"), ("bd1", "bd2")],
    },
    Step {
        head: "lam",
        cong: "def_eq_fuel_lam_cong",
        binders: "(ty1 : KExpr) (bd1 : KExpr) (ty2 : KExpr) (bd2 : KExpr)",
        na: "(KExpr.lam ty1 bd1)",
        nb: "(KExpr.lam ty2 bd2)",
        comps: &[("ty1", "ty2"), ("bd1", "bd2")],
    },
    Step {
        head: "app",
        cong: "def_eq_fuel_app_cong",
        binders: "(fn1 : KExpr) (ag1 : KExpr) (fn2 : KExpr) (ag2 : KExpr)",
        na: "(KExpr.app fn1 ag1)",
        nb: "(KExpr.app fn2 ag2)",
        comps: &[("fn1", "fn2"), ("ag1", "ag2")],
    },
    Step {
        head: "proj",
        cong: "def_eq_fuel_proj_cong",
        binders: "(ps : Name) (pidx : Nat) (sub1 : KExpr) (sub2 : KExpr)",
        na: "(KExpr.proj ps pidx sub1)",
        nb: "(KExpr.proj ps pidx sub2)",
        comps: &[("sub1", "sub2")],
    },
];

impl Specification {
    /// The per-head steps of the completeness recursion.
    pub(super) fn add_defeq_complete_steps(&mut self) -> Result<(), SpecError> {
        for (src, desc) in Self::complete_step_decls() {
            self.add_recursive_def(&src, &desc)?;
        }
        Ok(())
    }

    /// Generated so the shape tests read the proof terms, not this file's prose.
    fn complete_step_decls() -> Vec<(String, String)> {
        STEPS.iter().map(Self::one_step).collect()
    }

    fn one_step(st: &Step) -> (String, String) {
        let leg = |form: &str, which: &str| {
            format!(
                "(whnf_fuel_red_le the_red_env n (Nat.add n k) (le_add_self_left n k) \
                 {which} {form} h{which})"
            )
        };
        // Component acceptances, raised from the paired fuel k to n + k.
        let comp_at = |slot: usize| {
            let (l, r) = st.comps[slot];
            format!("(def_eq_fuel_le k (Nat.add n k) (le_add_self_right n k) {l} {r} hc{slot})")
        };

        // Unpack the paired acceptances, then apply the congruence.
        let (body, accept_binders) = if st.comps.len() == 2 {
            let (l0, r0) = st.comps[0];
            let (l1, r1) = st.comps[1];
            (
                format!(
                    "DefEqFuelAcceptsPair.rec {l0} {r0} {l1} {r1} \
                     (fun (_p : DefEqFuelAcceptsPair {l0} {r0} {l1} {r1}) => \
                     DefEqFuelAccepts a b) \
                     (fun (k : Nat) \
                     (hc0 : Eq Bool (def_eq_fuel the_red_env k {l0} {r0}) Bool.true) \
                     (hc1 : Eq Bool (def_eq_fuel the_red_env k {l1} {r1}) Bool.true) => \
                     DefEqFuelAccepts.mk a b (Nat.succ (Nat.add n k)) \
                     ({cong} (Nat.add n k) a b {args} {lega} {legb} {c0} {c1})) \
                     (def_eq_fuel_accepts_pair {l0} {r0} {l1} {r1} w0 w1)",
                    cong = st.cong,
                    args = st.binders_args(),
                    lega = leg(st.na, "a"),
                    legb = leg(st.nb, "b"),
                    c0 = comp_at(0),
                    c1 = comp_at(1),
                ),
                format!("(w0 : DefEqFuelAccepts {l0} {r0}) (w1 : DefEqFuelAccepts {l1} {r1})"),
            )
        } else {
            let (l0, r0) = st.comps[0];
            (
                format!(
                    "DefEqFuelAccepts.rec {l0} {r0} \
                     (fun (_p : DefEqFuelAccepts {l0} {r0}) => DefEqFuelAccepts a b) \
                     (fun (k : Nat) \
                     (hc0 : Eq Bool (def_eq_fuel the_red_env k {l0} {r0}) Bool.true) => \
                     DefEqFuelAccepts.mk a b (Nat.succ (Nat.add n k)) \
                     ({cong} (Nat.add n k) a b {args} {lega} {legb} {c0})) w0",
                    cong = st.cong,
                    args = st.binders_args(),
                    lega = leg(st.na, "a"),
                    legb = leg(st.nb, "b"),
                    c0 = comp_at(0),
                ),
                format!("(w0 : DefEqFuelAccepts {l0} {r0})"),
            )
        };

        let src = format!(
            "def def_eq_complete_step_{head} (n : Nat) (a : KExpr) (b : KExpr) {binders} \
             (ha : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) \
             (OptionType.some KExpr {na})) \
             (hb : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n b) \
             (OptionType.some KExpr {nb})) {accept_binders} : DefEqFuelAccepts a b := {body}",
            head = st.head,
            binders = st.binders,
            na = st.na,
            nb = st.nb,
        );

        let desc = format!(
            "def_eq_complete_step_{head}: the completeness recursion's {head} STEP — component \
             acceptances in, a composite acceptance out. \
             \
             Its whole job is a fuel collapse. Three fuels arrive independent of one another: the \
             whnf legs sit at n, and each component acceptance hides its own. The congruence \
             {cong} demands ONE fuel for all of them. So the component acceptances are paired to \
             a shared k, then the legs are raised from n and the components from k to n + k — \
             whnf_fuel_red_le on one side, def_eq_fuel_le on the other — and the congruence \
             applies there, giving an acceptance at n + k + 1. \
             \
             Doing this once per head rather than inline is what keeps the capstone's eight leaves \
             short, and it isolates the only genuinely fiddly arithmetic in the development. \
             \
             The component acceptances are HYPOTHESES: this is a step of the recursion, not the \
             recursion. The induction on rbelow_plus_acc that produces them is the capstone. \
             DerivedProved, zero axiom_deps.",
            head = st.head,
            cong = st.cong,
        );
        (src, desc)
    }
}

impl Step {
    /// The payload binder names, positionally, for the congruence application.
    fn binders_args(&self) -> String {
        self.binders
            .split(") (")
            .map(|b| {
                b.trim_start_matches('(')
                    .trim_end_matches(')')
                    .split(" : ")
                    .next()
                    .unwrap_or("")
                    .to_string()
            })
            .collect::<Vec<_>>()
            .join(" ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn terms() -> Vec<String> {
        Specification::complete_step_decls()
            .into_iter()
            .map(|(src, _)| src)
            .collect()
    }

    /// One step per recursive head, and `let_` deliberately absent — three
    /// components need a chained pairing and land once this pattern verifies.
    #[test]
    fn test_one_step_per_head() {
        assert_eq!(STEPS.len(), 4);
        let heads: Vec<&str> = STEPS.iter().map(|s| s.head).collect();
        for h in ["pi", "lam", "app", "proj"] {
            assert!(heads.contains(&h), "missing step for {h}");
        }
        assert!(
            !heads.contains(&"let"),
            "let_ is deliberately deferred: three components need a chained pairing"
        );
    }

    /// THE POINT OF THIS MODULE. Every step must raise BOTH whnf legs from `n`
    /// and EVERY component from `k`, to the same `n + k`. Missing any one leaves
    /// the congruence applied at mismatched fuels — which fails only inside a
    /// 21-minute build, and only after everything else typechecks.
    #[test]
    fn test_every_step_collapses_all_fuels_to_one_bound() {
        for (st, src) in STEPS.iter().zip(terms()) {
            assert_eq!(
                src.matches("whnf_fuel_red_le the_red_env n (Nat.add n k)")
                    .count(),
                2,
                "{}: both whnf legs must be raised from n to n + k",
                st.head
            );
            assert_eq!(
                src.matches("def_eq_fuel_le k (Nat.add n k)").count(),
                st.comps.len(),
                "{}: every component must be raised from k to n + k",
                st.head
            );
            assert!(
                src.contains(&format!("{} (Nat.add n k) a b", st.cong)),
                "{}: the congruence must be applied at the shared bound n + k",
                st.head
            );
            assert!(
                src.contains("DefEqFuelAccepts.mk a b (Nat.succ (Nat.add n k))"),
                "{}: the result sits one fuel level above the shared bound",
                st.head
            );
        }
    }

    /// Two-component heads pair their acceptances; the one-component head does
    /// not need to. Pairing where it is not needed, or omitting it where it is,
    /// both produce fuel mismatches.
    #[test]
    fn test_pairing_matches_component_count() {
        for (st, src) in STEPS.iter().zip(terms()) {
            let paired = src.contains("def_eq_fuel_accepts_pair");
            assert_eq!(
                paired,
                st.comps.len() > 1,
                "{}: pairing is needed exactly when there is more than one component",
                st.head
            );
        }
    }

    /// The component acceptances must be HYPOTHESES. If a step ever recursed on
    /// `rbelow_plus_acc` it would be the capstone wearing a step's name.
    #[test]
    fn test_steps_do_not_recurse() {
        for (st, src) in STEPS.iter().zip(terms()) {
            assert!(
                !src.contains("rbelow_plus_acc"),
                "{}: a step must take its component acceptances as hypotheses; recursing here \
                 would be the capstone in disguise",
                st.head
            );
            for (l, r) in st.comps {
                assert!(
                    src.contains(&format!("DefEqFuelAccepts {l} {r}")),
                    "{}: component ({l}, {r}) must appear as an acceptance hypothesis",
                    st.head
                );
            }
        }
    }

    #[test]
    fn test_step_terms_parens_balanced() {
        for (st, src) in STEPS.iter().zip(terms()) {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0, "{}: close paren before its open", st.head);
            }
            assert_eq!(depth, 0, "{}: unbalanced parens", st.head);
        }
    }
}
