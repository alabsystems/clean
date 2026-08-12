// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Non-vacuity of the wh3 completeness capstone.**
//!
//! `def_eq_fuel_complete_wh3_final` is a conditional theorem over `Wh3NormAcc`.
//! Before this module, **nothing in the specification concluded `Wh3NormAcc` at
//! a concrete term** — its only producers (`wh3_norm_acc_inv`,
//! `whnf_component_norm_acc_wh3`) each *consume* a `Wh3NormAcc`, so the supply
//! was circular. An empty predicate and a satisfiable one would have looked
//! identical to every gate, because a vacuous theorem's axiom closure is
//! impeccable. This programme has already been caught by that four times.
//!
//! So the floor is built here, and the capstone is *run*:
//!
//! ```text
//! wh3_norm_acc_sort                       : Wh3NormAcc (KExpr.sort Level.zero)
//! def_eq_fuel_complete_wh3_final_witness  : DefEqFuelAcceptsWh3 (sort 0) (sort 0)
//! ```
//!
//! ## Why a sort is the right floor
//!
//! `Wh3NormAcc` has two fields. The fuel field is `Eq.refl`: at fuel one the
//! `sort` arm of `reduce_once_red_wh3` is the literal `WhStepR.wstuck` and
//! `wh_dispatch3` maps `wstuck` to `some e0`. The hereditary field is
//! discharged by **absurdity** — the `wbelow3_plus`-closure of a sort is empty,
//! because `wbelow3`'s `red` arm needs a `wstep` where the sort arm gives
//! `wstuck`, and its `sub` arm needs a `subexpr_step` into a sort, which has no
//! arm at all.
//!
//! ## What this does NOT show
//!
//! A floor, not a reach. `Wh3NormAcc` is hereditary over reduct-**and-subterm**
//! descent, so it excludes every term carrying a non-normalising subterm
//! anywhere — including positions the algorithm never visits, such as the body
//! of a lambda the loop returns on immediately. Extending the witnessed class
//! is separate work.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const SRC_SUBEXPR_SORT: &str = "def subexpr_step_sort_absurd (x : KExpr) (sn : Level) (C : Type) (h : subexpr_step x (KExpr.sort sn)) : C := subexpr_step.rec (fun (aa : KExpr) (bb : KExpr) (_h : subexpr_step aa bb) => forall (C : Type) (sn : Level), Eq KExpr bb (KExpr.sort sn) -> C) (fun (f : KExpr) (a : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.app f a) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.app f a) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (f : KExpr) (a : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.app f a) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.app f a) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (ty : KExpr) (body : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.lam ty body) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (ty : KExpr) (body : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.lam ty body) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.lam ty body) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (ty : KExpr) (body : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.pi ty body) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.pi ty body) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (ty : KExpr) (body : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.pi ty body) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.pi ty body) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.let_ ty val body) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.let_ ty val body) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (ty : KExpr) (val : KExpr) (body : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.let_ ty val body) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.let_ ty val body) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) (fun (s : Name) (i : Nat) (sub : KExpr) (C : Type) (sn : Level) (heq : Eq KExpr (KExpr.proj s i sub) (KExpr.sort sn)) => kexpr_discr_t C (KExpr.proj s i sub) (KExpr.sort sn) heq (Eq.refl Bool Bool.false)) x (KExpr.sort sn) h C sn (Eq.refl KExpr (KExpr.sort sn))";

const SRC_WBELOW3_SORT: &str = "def wbelow3_sort_absurd (x : KExpr) (sn : Level) (C : Type) (h : wbelow3 x (KExpr.sort sn)) : C := wbelow3.rec x (KExpr.sort sn) (fun (_h : wbelow3 x (KExpr.sort sn)) => C) (fun (k : Nat) (hr : Eq WhStepR (reduce_once_red_wh3 the_red_env (fun (z : KExpr) => whnf_fuel_red_wh3 the_red_env k z) (KExpr.sort sn)) (WhStepR.wstep x)) => wh_stuck_ne_step_type x C hr) (fun (hs : subexpr_step x (KExpr.sort sn)) => subexpr_step_sort_absurd x sn C hs) h";

const SRC_WBELOW3_PLUS_SORT: &str = "def wbelow3_plus_sort_absurd (x : KExpr) (sn : Level) (C : Type) (h : wbelow3_plus x (KExpr.sort sn)) : C := wbelow3_plus.rec (fun (aa : KExpr) (bb : KExpr) (_h : wbelow3_plus aa bb) => forall (C : Type) (sn : Level), Eq KExpr bb (KExpr.sort sn) -> C) (fun (x2 : KExpr) (y2 : KExpr) (hb : wbelow3 x2 y2) (C2 : Type) (sn2 : Level) (heq : Eq KExpr y2 (KExpr.sort sn2)) => wbelow3_sort_absurd x2 sn2 C2 (Eq.substType KExpr (fun (Z : KExpr) => wbelow3 x2 Z) y2 (KExpr.sort sn2) heq hb)) (fun (x3 : KExpr) (y3 : KExpr) (z3 : KExpr) (_hb : wbelow3 x3 y3) (_hp : wbelow3_plus y3 z3) (ih : forall (C3 : Type) (sn3 : Level), Eq KExpr z3 (KExpr.sort sn3) -> C3) (C4 : Type) (sn4 : Level) (heq : Eq KExpr z3 (KExpr.sort sn4)) => ih C4 sn4 heq) x (KExpr.sort sn) h C sn (Eq.refl KExpr (KExpr.sort sn))";

const SRC_NORM_ACC_SORT: &str = "def wh3_norm_acc_sort : Wh3NormAcc (KExpr.sort Level.zero) := Wh3NormAcc.intro (KExpr.sort Level.zero) (WhnfFuelReachesWh3.mk (KExpr.sort Level.zero) (Nat.succ Nat.zero) (KExpr.sort Level.zero) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero)))) (fun (e2 : KExpr) (hb : wbelow3_plus e2 (KExpr.sort Level.zero)) => wbelow3_plus_sort_absurd e2 Level.zero (Wh3NormAcc e2) hb)";

const SRC_COMPLETE_WITNESS: &str = "def def_eq_fuel_complete_wh3_final_witness : DefEqFuelAcceptsWh3 (KExpr.sort Level.zero) (KExpr.sort Level.zero) := def_eq_fuel_complete_wh3_final (KExpr.sort Level.zero) wh3_norm_acc_sort (KExpr.sort Level.zero) (DefEq.refl (KExpr.sort Level.zero)) wh3_norm_acc_sort";

impl Specification {
    /// The inhabitation floor, and the capstone run at it.
    pub(super) fn add_wh3_norm_acc_witness(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(SRC_SUBEXPR_SORT, "subexpr_step_sort_absurd: a sort has no subexpressions. Ten arms of subexpr_step.rec, every one concluding at app/lam/pi/let_/proj and dying by kexpr_discr_t -- an argument from an ABSENT constructor, since subexpr_step has no sort arm. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WBELOW3_SORT, "wbelow3_sort_absurd: nothing is wbelow3 a sort. Two arms: the red arm needs the three-way step to report wstep at a sort, but the sort arm of reduce_once_red_wh3 is the literal constant WhStepR.wstuck, so wh_stuck_ne_step_type kills it; the sub arm is subexpr_step_sort_absurd. \
\
Note the recursor convention, which cost a cycle: BOTH of wbelow3's arguments are PARAMETERS (they lead, they are uniform across both constructors, and there is no recursive occurrence), so wbelow3.rec takes them before the motive and the target is already fixed -- no convoy is needed. wbelow3_plus is different: its step arm recurses on wbelow3_plus y z, a DIFFERENT first argument, which disqualifies that argument as a parameter. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WBELOW3_PLUS_SORT, "wbelow3_plus_sort_absurd: nothing is in the transitive closure below a sort either. Base delegates to wbelow3_sort_absurd; step walks up to its own induction hypothesis. Both arguments are indices here, unlike wbelow3. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_NORM_ACC_SORT, "wh3_norm_acc_sort: *** Wh3NormAcc IS INHABITED. *** A concrete value of Wh3NormAcc (KExpr.sort Level.zero). \
\
The fuel field is Eq.refl: at fuel one the sort arm reports wstuck and wh_dispatch3 maps wstuck to some e0, so whnf_fuel_red_wh3 the_red_env 1 (sort 0) computes to some (sort 0). The hereditary field is discharged by absurdity, because the wbelow3_plus-closure of a sort is EMPTY. \
\
This is the floor the predicate needed. Before it, nothing in the specification concluded Wh3NormAcc at a concrete term -- its only producers consumed a Wh3NormAcc, so the supply was circular and an empty predicate would have looked identical. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_COMPLETE_WITNESS, "def_eq_fuel_complete_wh3_final_witness: *** THE COMPLETENESS THEOREM IS NOT VACUOUS. *** Instantiates def_eq_fuel_complete_wh3_final at a concrete term carrying a concrete Wh3NormAcc value, yielding DefEqFuelAcceptsWh3 (sort 0) (sort 0). \
\
A conditional theorem whose antecedent is uninhabited is worthless AND passes every gate in this repository, because the axiom closure of a vacuous statement is impeccable. This programme has hit that failure four times. The theorem's type alone could not distinguish 'complete' from 'empty'; this witness does, by running it. \
\
It does NOT establish that the useful cases are covered -- Wh3NormAcc is hereditary over reduct-and-subterm descent, so it excludes any term with a non-normalising subterm anywhere, including positions the algorithm never visits. It establishes a floor, not a reach. DerivedProved, zero axiom_deps.")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The floor must CONCLUDE `Wh3NormAcc` at a concrete term while consuming
    /// none. If it ever takes a `Wh3NormAcc` argument the supply is circular
    /// again and the predicate is unwitnessed.
    #[test]
    fn test_floor_consumes_no_wh3normacc() {
        let i = SRC_NORM_ACC_SORT.find(":=").expect("has a body");
        let (ty, body) = SRC_NORM_ACC_SORT.split_at(i);
        assert!(
            ty.contains(": Wh3NormAcc (KExpr.sort Level.zero)"),
            "must conclude at a concrete term"
        );
        assert!(
            !ty.contains("(h : Wh3NormAcc"),
            "must not consume a Wh3NormAcc"
        );
        assert!(body.contains("Wh3NormAcc.intro"), "must build one directly");
    }

    /// The hereditary field must be discharged by ABSURDITY, not by assuming
    /// something below the sort is accessible.
    #[test]
    fn test_hereditary_field_is_discharged_by_absurdity() {
        assert!(SRC_NORM_ACC_SORT.contains("wbelow3_plus_sort_absurd"));
    }

    /// The witness must actually apply the capstone — that is the whole point.
    #[test]
    fn test_witness_runs_the_capstone() {
        assert!(SRC_COMPLETE_WITNESS.contains("def_eq_fuel_complete_wh3_final"));
        assert!(SRC_COMPLETE_WITNESS.contains(": DefEqFuelAcceptsWh3"));
    }

    #[test]
    fn test_sources_balanced_ascii_prime_free() {
        for src in [
            SRC_SUBEXPR_SORT,
            SRC_WBELOW3_SORT,
            SRC_WBELOW3_PLUS_SORT,
            SRC_NORM_ACC_SORT,
            SRC_COMPLETE_WITNESS,
        ] {
            let mut depth: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => depth += 1,
                    ')' => depth -= 1,
                    _ => {}
                }
                assert!(depth >= 0);
            }
            assert_eq!(depth, 0, "unbalanced parens");
            assert!(src.is_ascii());
            assert!(!src.contains('\''));
        }
    }
}
