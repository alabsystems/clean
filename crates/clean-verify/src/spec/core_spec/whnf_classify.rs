// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Classification of the executable loop's result, and the completeness
//! capstone's target type.
//!
//! ## Why classification cannot be premise-free
//!
//! `whnf_shape.rs` rules out `let_` and β-redex heads with no hypotheses at
//! all. That is as far as premise-free reasoning goes. Deciding whether an
//! `app f a` in normal form is *neutral* — that its head is not a lambda and
//! not a δ- or ι-redex — requires knowing that the head constant has no
//! definition in the environment, which is exactly `consts_defined_red`; and
//! ruling out open-term pathologies requires `red_closed_at`. So the general
//! nine-way head classification is genuinely conditional, and pretending
//! otherwise would be the kind of quiet premise-dropping this program exists to
//! prevent.
//!
//! What can be minimised is *how many* premises and *where* they sit:
//!
//! | route | premises |
//! |---|---|
//! | `whnf_fuel_red_classifies` (`whnf_progress.rs:2109`) | `red_env_good` + `red_closed_at e 0` + `consts_defined_red e`, on the INPUT |
//! | `reduce_once_red_none_classifies` (`:2062`) | `red_closed_at` + `consts_defined_red`, on the FIXPOINT |
//! | `whnf_fuel_red_classifies_at_result` (here) | the same two, on the RESULT |
//!
//! Composing `whnf_fuel_red_no_redex` — unconditional — with the fixpoint
//! classifier drops `red_env_good` entirely. The price is that the two
//! remaining premises are about the normal form rather than the input; pushing
//! them back to the input needs `reduce_once_red_preserves_closed` /
//! `_preserves_defined`, and **both of those require `red_env_good`**
//! (`whnf_progress.rs:1882`, `:1967`), which is why the existing input-side
//! classifier carries it.
//!
//! ## `red_env_good the_red_env` is not discharged anywhere
//!
//! Worth recording plainly: it appears in the tree only ever as a carried
//! hypothesis — no lemma concludes it. It is a conjunction of closedness and
//! well-formedness conditions on the 50 definitions and 38 recursor rules of
//! `kernel_core_red_env`, so it ought to be discharged by the same single-`rfl`
//! checker route that discharged `RedEnvFaithful`
//! (`faithful_checkers.rs:932-1010`). Until someone builds that checker, any
//! theorem needing input-side classification carries it, and should say so.
//!
//! ## `DefEqFuelAccepts`
//!
//! Also registered here: the type the completeness capstone concludes with.
//! Defining the target is not proving anything — the capstone itself is still
//! unwritten — but the type has to exist before the statement can be made, and
//! the spec has no `Exists`, so it is the usual single-constructor witness.
//!
//! `DerivedProved`, empty axiom closures; the witness is census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Result-side classification and the capstone's target type.
    pub(super) fn add_whnf_classify(&mut self) -> Result<(), SpecError> {
        self.add_result_classification()?;
        self.add_defeq_fuel_accepts()?;
        Ok(())
    }

    fn add_result_classification(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def whnf_fuel_red_classifies_at_result (n : Nat) (e : KExpr) (r : KExpr) \
             (h : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n e) \
             (OptionType.some KExpr r)) \
             (hc : red_closed_at r Nat.zero) \
             (hd : consts_defined_red the_red_env r) : whnf_noredex_class r := \
             reduce_once_red_none_classifies r \
             (whnf_fuel_red_no_redex the_red_env n e r h) hc hd",
            "whnf_fuel_red_classifies_at_result: the executable loop's RESULT classifies — it is \
             a landed is_whnf value or an honest stuck application / projection residual. \
             Composes the UNCONDITIONAL whnf_fuel_red_no_redex with the fixpoint classifier, \
             which drops the red_env_good premise that whnf_fuel_red_classifies carries. The two \
             surviving premises (red_closed_at, consts_defined_red) are genuinely needed and are \
             stated on the RESULT, where the classifier consumes them: deciding whether a normal \
             form's application head is neutral means knowing its head constant has no definition \
             in the environment. Pushing them back to the input requires the preservation lemmas, \
             and BOTH of those require red_env_good — which nothing in the tree discharges. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    fn add_defeq_fuel_accepts(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive DefEqFuelAccepts (a : KExpr) (b : KExpr) : Type\n\
             | mk : forall (n : Nat), Eq Bool (def_eq_fuel the_red_env n a b) Bool.true -> \
             DefEqFuelAccepts a b",
            "DefEqFuelAccepts a b: SOME fuel is enough for the structural conversion algorithm to \
             accept a against b. The conclusion the completeness capstone must reach. The spec \
             has no Exists and no Sigma, so this is a single-constructor witness inductive (the \
             par_strips_witness_cd_star idiom). Registering the TARGET TYPE is not a completeness \
             claim -- the capstone is unwritten -- but the type must exist before the statement \
             can be made, and having it here keeps the eventual statement honest about its \
             quantifier. Census-neutral.",
        )?;

        // Raising the witness's fuel: immediate from def_eq_fuel_le, and the
        // capstone needs it to combine per-component acceptances.
        self.add_recursive_def(
            "def def_eq_fuel_accepts_le (a : KExpr) (b : KExpr) (m : Nat) \
             (w : DefEqFuelAccepts a b) \
             (hb : forall (k : Nat), Eq Bool (def_eq_fuel the_red_env k a b) Bool.true -> \
             Le k m) : Eq Bool (def_eq_fuel the_red_env m a b) Bool.true := \
             DefEqFuelAccepts.rec a b \
             (fun (_w : DefEqFuelAccepts a b) => \
             Eq Bool (def_eq_fuel the_red_env m a b) Bool.true) \
             (fun (n : Nat) (hn : Eq Bool (def_eq_fuel the_red_env n a b) Bool.true) => \
             def_eq_fuel_le n m (hb n hn) a b hn) w",
            "def_eq_fuel_accepts_le: cash a DefEqFuelAccepts witness at any fuel bound the \
             witness's own fuel is below. The bound is supplied as a function of the witnessed \
             fuel because that fuel is existentially hidden inside the witness -- the caller \
             cannot name it, so it must be able to bound whatever it turns out to be. This is how \
             the capstone will combine per-component acceptances, which come back at different \
             fuels, into one acceptance at a common bound. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    /// The result-side classifier must NOT reintroduce `red_env_good` — that
    /// is the entire reason it exists rather than calling
    /// `whnf_fuel_red_classifies` directly.
    #[test]
    fn test_result_classification_drops_red_env_good() {
        let src = include_str!("whnf_classify.rs");
        let term_start = src
            .find("def whnf_fuel_red_classifies_at_result")
            .expect("declaration present");
        let term_end = src[term_start..]
            .find("\",\n")
            .expect("declaration string terminates")
            + term_start;
        let term = &src[term_start..term_end];
        assert!(
            !term.contains("red_env_good"),
            "the result-side classifier must not carry red_env_good"
        );
        assert!(
            term.contains("whnf_fuel_red_no_redex"),
            "it must route through the unconditional no-redex fact"
        );
        assert!(
            term.contains("red_closed_at r Nat.zero")
                && term.contains("consts_defined_red the_red_env r"),
            "the two surviving premises must be stated on the RESULT r, not on the input e"
        );
    }
}
