// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Link 4 of the def-eq completeness chain: **fuel adequacy**.
//!
//! The scoping audit called this "the single largest hole": nothing in the tree
//! connected `whnf_acc` / `below_plus_acc` to any concrete fuel bound, and
//! `below_plus_acc` — built as step 1 of this program — had **zero consumers
//! anywhere**. This closes that: from a well-foundedness witness, produce a
//! fuel at which the executable whnf loop actually returns.
//!
//! ```text
//! whnf_fuel_from_acc : forall (e : KExpr), rbelow_plus_acc e -> WhnfFuelReaches e
//! ```
//!
//! ## Why a new order rather than `below`
//!
//! `below`'s `red` arm is over `whnf_step` (`whnf_reduction.rs:137`, `:364`),
//! but the algorithm runs `whnf_red_step` (`whnf_progress.rs:4219`). The two
//! are not the same relation, and the containment `whnf_red_step ⊆ whnf_step`
//! is genuine work: four of its five arms are constructor maps, but `app_left`
//! is recursive and its δ/ι sub-cases need a spine-append lemma about
//! `delta_reduct`, which unfolds the head const of a whole application spine
//! (`delta_step.rs:61`).
//!
//! So `rbelow` re-bases the order on the relation the algorithm actually
//! steps by. **This reverses a warning I wrote in the plan doc earlier today**,
//! which said re-basing was the more expensive option because it means
//! rebuilding three inductives. That comparison was wrong: three inductives are
//! ~20 lines and census-neutral, while the spine development is multi-lemma.
//! And the stated reason not to re-base — that `below_plus_acc` is "the witness
//! the SN-parametric engine consumes" — does not hold either, because that
//! engine does not exist yet and `below_plus_acc` has no consumers to break.
//!
//! `below` and friends are deliberately left in place: the containment is still
//! worth having (it would let a `below_plus_acc` witness be converted into an
//! `rbelow_plus_acc` one), and `beta_reduces_bd_to_beta_reduces` — its first
//! sub-goal — is already landed in `beta_bd_embedding.rs`.
//!
//! ## The construction
//!
//! Accessibility recursion on `e`, case-splitting on the executable step:
//!
//! - `reduce_once_red the_red_env x = none` — `x` is already a fixpoint of the
//!   loop, so **fuel 1 suffices** and returns `x` itself.
//! - `reduce_once_red the_red_env x = some x2` — then `whnf_red_step the_red_env
//!   x x2` (`reduce_once_red_sound`), so `x2` is one `rbelow` step below `x`;
//!   the induction hypothesis supplies a fuel `n` for `x2`, and `n+1` works for
//!   `x`.
//!
//! Both cases go through `whnf_fuel_red_succ_dispatch`, which unfolds one layer
//! of the loop. It is stated with an **explicit lambda**
//! (`fun z => whnf_fuel_red renv k z`) rather than the partial application
//! `whnf_fuel_red renv k`: the two differ by η, and writing the lambda makes
//! the equation hold by β alone, so the proof does not depend on the checker's
//! η behaviour.
//!
//! ## What this does and does not give
//!
//! It gives the missing quantifier: *there is* a fuel. It does **not** give the
//! capstone, which additionally needs the head-rigidity inversions for
//! `proj`/`lit`/`bvar`/`let_` (only sort/lam/pi/neutral-app/dead-const exist),
//! fuel monotonicity for `def_eq_fuel`, and the descent argument placing whnf
//! components below their originals in `rbelow_plus`.
//!
//! Every declaration is `DerivedProved` with an empty axiom closure; the three
//! inductives are census-neutral (Inductive/Constructor/Recursor, no axioms).

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The algorithm-matched well-founded order, the fuel witness, and the
    /// accessibility-to-fuel construction.
    pub(super) fn add_fuel_adequacy(&mut self) -> Result<(), SpecError> {
        self.add_rbelow_order()?;
        self.add_whnf_fuel_witness()?;
        self.add_whnf_fuel_from_acc()?;
        Ok(())
    }

    /// `rbelow` / `rbelow_plus` / `rbelow_plus_acc` — the same three-inductive
    /// shape as `below`, but with the `red` arm over `whnf_red_step
    /// the_red_env`, the relation the executable loop actually steps by.
    fn add_rbelow_order(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive rbelow : KExpr -> KExpr -> Type\n\
             | red : forall (x : KExpr) (y : KExpr), whnf_red_step the_red_env y x -> rbelow x y\n\
             | sub : forall (x : KExpr) (y : KExpr), subexpr_step x y -> rbelow x y",
            "rbelow x y: x lies one step below y in the order the CONVERSION ALGORITHM descends \
             on — either y takes one executable weak-head step TO x (note the reversed argument \
             order, since reduction goes downward) or x is an immediate subexpression of y. \
             Identical in shape to `below`, but its red arm is whnf_red_step the_red_env rather \
             than whnf_step: whnf_step is what `below` was built over before the algorithm \
             existed, and the two relations are not the same. Census-neutral.",
        )?;

        self.add_inductive(
            "inductive rbelow_plus : KExpr -> KExpr -> Type\n\
             | base : forall (x : KExpr) (y : KExpr), rbelow x y -> rbelow_plus x y\n\
             | step : forall (x : KExpr) (y : KExpr) (z : KExpr), rbelow x y -> \
             rbelow_plus y z -> rbelow_plus x z",
            "rbelow_plus: the transitive closure of rbelow. The completeness recursion descends \
             on this rather than on rbelow because a single conversion round both reduces and \
             then enters a subterm. Census-neutral.",
        )?;

        self.add_inductive(
            "inductive rbelow_plus_acc : KExpr -> Type\n\
             | intro : forall (e : KExpr), (forall (e2 : KExpr), rbelow_plus e2 e -> \
             rbelow_plus_acc e2) -> rbelow_plus_acc e",
            "rbelow_plus_acc e: e is accessible in the transitive rbelow order — every term \
             strictly below e is itself accessible. THE well-foundedness witness the conversion \
             algorithm's termination argument consumes. Permanently a hypothesis, not something \
             to be discharged internally: discharging it for all terms is strong normalisation, \
             which by Godel-2 cannot be proved inside the system it is about. Census-neutral.",
        )?;

        Ok(())
    }

    /// `WhnfFuelReaches e` — the packaged "some fuel suffices" existential.
    fn add_whnf_fuel_witness(&mut self) -> Result<(), SpecError> {
        // `e` is declared as a genuine PARAMETER rather than left as an index.
        // The constructor makes no recursive reference, so the kernel's
        // fixed-indices-to-parameters pass would promote it anyway; writing it
        // explicitly pins the recursor shape instead of depending on that pass.
        self.add_inductive(
            "inductive WhnfFuelReaches (e : KExpr) : Type\n\
             | mk : forall (n : Nat) (r : KExpr), \
             Eq (OptionType KExpr) (whnf_fuel_red the_red_env n e) (OptionType.some KExpr r) -> \
             WhnfFuelReaches e",
            "WhnfFuelReaches e packages a fuel n and a result r with a proof that the executable \
             whnf loop run on e at fuel n returns r. The spec has no Exists and no Sigma, so \
             every existential is a single-constructor witness inductive — the \
             par_strips_witness_cd_star idiom. This is the statement 'some fuel is enough for \
             e', which is exactly what fuel adequacy has to produce and what nothing in the tree \
             could previously express. Census-neutral.",
        )?;
        Ok(())
    }

    /// One unfolding of the fuel loop, then the accessibility recursion.
    fn add_whnf_fuel_from_acc(&mut self) -> Result<(), SpecError> {
        // The loop layer. Stated with an explicit lambda for the recursive
        // slot: `whnf_fuel_red renv k` and `fun z => whnf_fuel_red renv k z`
        // differ by eta, and the explicit form makes this hold by beta alone.
        self.add_recursive_def(
            "def whnf_fuel_red_succ_dispatch (renv : RedEnv) (k : Nat) (e : KExpr) : \
             Eq (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e) \
             (loop_dispatch (reduce_once_red renv e) e \
             (fun (z : KExpr) => whnf_fuel_red renv k z)) := \
             Eq.refl (OptionType KExpr) (whnf_fuel_red renv (Nat.succ k) e)",
            "whnf_fuel_red_succ_dispatch: one layer of the executable whnf loop — at fuel k+1 \
             the loop takes one executable step and continues at fuel k (Eq.refl, definitional). \
             The continuation is written as an explicit lambda rather than the partial \
             application whnf_fuel_red renv k, which differs from it by eta; with the lambda the \
             equation closes by beta alone and the proof does not depend on the checker's eta \
             behaviour. DerivedProved, zero axiom_deps.",
        )?;

        // Fuel 1 on a term the executable step cannot reduce: the loop returns
        // the term itself.
        self.add_recursive_def(
            "def whnf_fuel_red_one_of_stuck (e : KExpr) \
             (hn : Eq (OptionType KExpr) (reduce_once_red the_red_env e) (OptionType.none KExpr)) : \
             Eq (OptionType KExpr) (whnf_fuel_red the_red_env (Nat.succ Nat.zero) e) \
             (OptionType.some KExpr e) := \
             Eq.trans (OptionType KExpr) \
             (whnf_fuel_red the_red_env (Nat.succ Nat.zero) e) \
             (loop_dispatch (reduce_once_red the_red_env e) e \
             (fun (z : KExpr) => whnf_fuel_red the_red_env Nat.zero z)) \
             (OptionType.some KExpr e) \
             (whnf_fuel_red_succ_dispatch the_red_env Nat.zero e) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) \
             (fun (o : OptionType KExpr) => loop_dispatch o e \
             (fun (z : KExpr) => whnf_fuel_red the_red_env Nat.zero z)) \
             (reduce_once_red the_red_env e) (OptionType.none KExpr) hn)",
            "whnf_fuel_red_one_of_stuck: if the executable step has nothing to do on e then ONE \
             unit of fuel suffices and the loop returns e itself. This is the base case of fuel \
             adequacy, and it is a computation rather than an argument because loop_dispatch \
             returns its input on a none reduct. DerivedProved, zero axiom_deps.",
        )?;

        // Fuel n+1 on a term that steps: whatever fuel worked for the reduct.
        self.add_recursive_def(
            "def whnf_fuel_red_succ_of_step (e : KExpr) (e2 : KExpr) (n : Nat) (r : KExpr) \
             (hs : Eq (OptionType KExpr) (reduce_once_red the_red_env e) \
             (OptionType.some KExpr e2)) \
             (hr : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n e2) \
             (OptionType.some KExpr r)) : \
             Eq (OptionType KExpr) (whnf_fuel_red the_red_env (Nat.succ n) e) \
             (OptionType.some KExpr r) := \
             Eq.trans (OptionType KExpr) \
             (whnf_fuel_red the_red_env (Nat.succ n) e) \
             (loop_dispatch (reduce_once_red the_red_env e) e \
             (fun (z : KExpr) => whnf_fuel_red the_red_env n z)) \
             (OptionType.some KExpr r) \
             (whnf_fuel_red_succ_dispatch the_red_env n e) \
             (Eq.trans (OptionType KExpr) \
             (loop_dispatch (reduce_once_red the_red_env e) e \
             (fun (z : KExpr) => whnf_fuel_red the_red_env n z)) \
             (loop_dispatch (OptionType.some KExpr e2) e \
             (fun (z : KExpr) => whnf_fuel_red the_red_env n z)) \
             (OptionType.some KExpr r) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) \
             (fun (o : OptionType KExpr) => loop_dispatch o e \
             (fun (z : KExpr) => whnf_fuel_red the_red_env n z)) \
             (reduce_once_red the_red_env e) (OptionType.some KExpr e2) hs) hr)",
            "whnf_fuel_red_succ_of_step: if e takes one executable step to e2 and fuel n suffices \
             for e2, then fuel n+1 suffices for e and returns the same result. The inductive \
             step of fuel adequacy. Rewriting the loop's scrutinee to `some e2` makes \
             loop_dispatch fire and beta-reduce to the recursive call, at which point hr closes \
             it. DerivedProved, zero axiom_deps.",
        )?;

        // THE THEOREM. Accessibility recursion; the case split is on the
        // executable step, generalised over the scrutinee (the convoy) because
        // `reduce_once_red the_red_env x` is not a constructor application.
        self.add_recursive_def(
            "def whnf_fuel_from_acc (e : KExpr) (acc : rbelow_plus_acc e) : WhnfFuelReaches e := \
             rbelow_plus_acc.rec \
             (fun (x0 : KExpr) (_h : rbelow_plus_acc x0) => WhnfFuelReaches x0) \
             (fun (x0 : KExpr) \
             (_hf : forall (y : KExpr), rbelow_plus y x0 -> rbelow_plus_acc y) \
             (ih : forall (y : KExpr), rbelow_plus y x0 -> WhnfFuelReaches y) => \
             OptionType.rec KExpr \
             (fun (o : OptionType KExpr) => \
             Eq (OptionType KExpr) (reduce_once_red the_red_env x0) o -> WhnfFuelReaches x0) \
             (fun (hn : Eq (OptionType KExpr) (reduce_once_red the_red_env x0) \
             (OptionType.none KExpr)) => \
             WhnfFuelReaches.mk x0 (Nat.succ Nat.zero) x0 \
             (whnf_fuel_red_one_of_stuck x0 hn)) \
             (fun (x2 : KExpr) \
             (hs : Eq (OptionType KExpr) (reduce_once_red the_red_env x0) \
             (OptionType.some KExpr x2)) => \
             WhnfFuelReaches.rec x2 \
             (fun (_w : WhnfFuelReaches x2) => WhnfFuelReaches x0) \
             (fun (n : Nat) (r : KExpr) \
             (hr : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n x2) \
             (OptionType.some KExpr r)) => \
             WhnfFuelReaches.mk x0 (Nat.succ n) r \
             (whnf_fuel_red_succ_of_step x0 x2 n r hs hr)) \
             (ih x2 (rbelow_plus.base x2 x0 (rbelow.red x2 x0 \
             (reduce_once_red_sound the_red_env x0 x2 hs))))) \
             (reduce_once_red the_red_env x0) \
             (Eq.refl (OptionType KExpr) (reduce_once_red the_red_env x0))) \
             e acc",
            "whnf_fuel_from_acc: FUEL ADEQUACY — from a well-foundedness witness for e in the \
             algorithm's own order, produce a fuel at which the executable whnf loop returns. \
             This is link 4 of the def-eq completeness chain and was the single largest hole in \
             the program: nothing connected accessibility to a concrete fuel bound, and the \
             order built for exactly this purpose had zero consumers. Accessibility recursion \
             with a case split on reduce_once_red: a none reduct means x is already a fixpoint \
             so fuel 1 suffices; a some reduct is a genuine whnf_red_step \
             (reduce_once_red_sound), hence one rbelow step down, so the induction hypothesis \
             applies to the reduct and its fuel plus one works for x. The scrutinee is \
             generalised (the convoy) because reduce_once_red the_red_env x is not a constructor \
             application and cannot be case-split directly. It supplies the missing quantifier \
             only — the completeness capstone additionally needs head-rigidity inversions for \
             proj/lit/bvar/let_, fuel monotonicity for def_eq_fuel, and the descent placing whnf \
             components below their originals. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}
