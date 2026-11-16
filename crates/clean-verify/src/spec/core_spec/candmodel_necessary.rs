// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **A NECESSARY CONDITION on `CandModel tenv`** — the first constraint derived
//! from the telescope itself rather than from a candidate that approximates it.
//!
//! Everything else on the inhabitation question
//! (`designs/2026-09-18-is-candmodel-uninhabited.md`) probes a SPECIFIC
//! candidate family and asks which laws it satisfies. That is diagnostic, and
//! §3d records why it cannot decide the question: the type-blind family fails
//! `pi_elim`, so it is not a model and no amount of further probing makes it
//! one.
//!
//! This module asks the opposite question and gets an answer. Take an ARBITRARY
//! `M : CandModel tenv` and compose two of its own fields:
//!
//! ```text
//! redConst : ... kdecl_type_at tenv n us = some A -> Red (psubst s A) (const n us)
//! cr1      : Red T e -> whnf_acc e
//! ```
//!
//! at `s := idsubst`. The composite is
//!
//! ```text
//! kdecl_type_at tenv n us = some A -> whnf_acc (const n us)
//! ```
//!
//! — a statement with no `Red` in it at all. So **every constant `tenv` assigns
//! a type to is forced to be strongly normalizing as a bare `const`**, and
//! `CandModel tenv` is UNINHABITED for any `tenv` that types a constant whose
//! δ-body in the fixed `the_red_env` diverges.
//!
//! # What this does and does not settle
//!
//! It does NOT refute `CandModel` here, and the reason is worth recording
//! because it was the first thing checked. `the_red_env := kernel_core_red_env`
//! is a mechanical reflection of the foundation core — Nat, Bool, Eq, Name,
//! KExpr, ListType, OptionType, Lt/Le, ProdType/AndType, Level, the RecEnv
//! family and the modeled fragment's own vocabulary — and those definitions
//! terminate. A constant with no δ-body at all is SN outright
//! (`whnfAcc_const`). So the hypothesis of the refutation is not satisfiable at
//! the env this spec fixes, and the route that looked like a cheap refutation
//! closes.
//!
//! What it leaves is a REAL obligation with a checkable shape, which is more
//! than the question had before: inhabitation is not a property of `CandModel`
//! alone but of the pair `(tenv, the_red_env)`, and the `tenv` side has a stated
//! necessary condition. A `CandModel`-conditional theorem quantified over an
//! arbitrary `tenv` is therefore quantified over some `tenv`s where the
//! hypothesis is provably empty — which is exactly the vacuity shape the
//! loop-(i) precedent warns about, now pinned rather than suspected.
//!
//! Both constants are `DerivedProved` with zero `axiom_deps`: census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

use super::dependent_sn_richmodel::CANDMODEL_MK_BINDERS;

impl Specification {
    /// `CandModel tenv` forces every `tenv`-typed constant to be `whnf_acc`.
    ///
    /// A `CandModel.rec` projection binding the whole fifteen-binder telescope
    /// and using exactly two of its fields. The motive re-quantifies `n`, `us`
    /// and `A` under fresh names so nothing shadows the outer binders.
    fn candmodel_forces_const_whnf_acc_src() -> String {
        let motive = "(fun (M0 : CandModel tenv) => \
                      forall (nn : Name) (uu : ListType Level) (AA : KExpr), \
                      @Eq (OptionType KExpr) (kdecl_type_at tenv nn uu) \
                      (@OptionType.some KExpr AA) -> whnf_acc (KExpr.const nn uu)) ";
        let minor = "fun (nn : Name) (uu : ListType Level) (AA : KExpr) \
                     (hh : @Eq (OptionType KExpr) (kdecl_type_at tenv nn uu) \
                     (@OptionType.some KExpr AA)) => \
                     cr1 (psubst idsubst AA) (KExpr.const nn uu) \
                     (redConst nn uu AA idsubst hh))";
        format!(
            "def candmodel_forces_const_whnf_acc \
             (tenv : KDeclEnv) (M : CandModel tenv) \
             (n : Name) (us : ListType Level) (A : KExpr) \
             (h : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) : \
             whnf_acc (KExpr.const n us) := \
             @CandModel.rec tenv {motive}{tele}{minor} M n us A h",
            tele = CANDMODEL_MK_BINDERS,
        )
    }

    /// The contrapositive, in the tree's own absurdity idiom (`forall (C :
    /// Type)`, there being no empty type registered here).
    ///
    /// This is the shape a refutation would be delivered in: exhibit a `tenv`
    /// typing a constant whose bare `const` form is provably NOT `whnf_acc`, and
    /// `CandModel tenv` is empty. The module doc records why no such constant
    /// exists at the env this spec fixes.
    fn candmodel_uninhabited_of_nonsn_const_src() -> String {
        "def candmodel_uninhabited_of_nonsn_const \
         (tenv : KDeclEnv) (n : Name) (us : ListType Level) (A : KExpr) \
         (h : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) \
         (hbad : forall (C : Type), whnf_acc (KExpr.const n us) -> C) \
         (M : CandModel tenv) (C : Type) : C := \
         hbad C (candmodel_forces_const_whnf_acc tenv M n us A h)"
            .to_string()
    }

    /// **Rung 2 of the necessary-condition ladder.** Elaborates in 0.5 s;
    /// WIRED, so `add_candmodel_necessary` registers it and the spec build is
    /// what keeps it honest. It was scratch-tested unwired first, because this
    /// vec is what that registrar iterates and a term that failed to elaborate
    /// would abort the spec build for every lane rather than fail one test.
    ///
    /// `CandModel tenv` forces every application of a declared FUNCTION constant
    /// to a strongly normalizing argument to be strongly normalizing.
    ///
    /// Strictly stronger than `candmodel_forces_const_whnf_acc`, and reached the
    /// same way: premise and conclusion both avoid the telescope's hidden `Red`,
    /// so the statement survives OUTSIDE the eliminator. That is the whole
    /// constraint on what this ladder can say, and it is what picks out the
    /// fields that can open one. Exactly two GENERATE a `Red` from `Red`-free
    /// premises: `redConst`, whose premise is a mere declaration lookup and is
    /// the only premise in the telescope that is neither a `Red` nor a
    /// `whnf_acc`, and `red_sort`, whose premise is a `whnf_acc`. (`cr3` opens
    /// too, but only at a term with no successors; `redTypeStep` has `Red`-free
    /// premises yet generates nothing, transporting a `Red` it is given.) This
    /// rung uses both real doors, one for the function and one for the
    /// argument.
    ///
    /// Four fields in one chain:
    ///
    /// 1. `redConst` gives `Red (psubst s A) (const n us)` from the declaration
    ///    alone;
    /// 2. transport along `psubst s A = pi (sort u) B` retypes that at a `pi`;
    /// 3. `red_sort` supplies the ARGUMENT's reducibility from `whnf_acc a` --
    ///    the second field with a `Red`-free premise, and the reason the domain
    ///    is restricted to a sort here rather than left arbitrary;
    /// 4. `pi_elim` then `cr1`.
    ///
    /// The substitution `s` stays universally quantified rather than fixed to
    /// `idsubst` as in rung 1, because a caller needs it free to reach a `pi`.
    fn candmodel_forces_app_const_whnf_acc_src() -> String {
        let motive = "(fun (M0 : CandModel tenv) => \
                      forall (nn : Name) (uu : ListType Level) (AA : KExpr) \
                      (ss : Nat -> KExpr) (uv : Level) (BB : KExpr) (aa : KExpr), \
                      @Eq (OptionType KExpr) (kdecl_type_at tenv nn uu) \
                      (@OptionType.some KExpr AA) -> \
                      @Eq KExpr (psubst ss AA) (KExpr.pi (KExpr.sort uv) BB) -> \
                      whnf_acc aa -> \
                      whnf_acc (KExpr.app (KExpr.const nn uu) aa)) ";
        let minor = "fun (nn : Name) (uu : ListType Level) (AA : KExpr) \
                     (ss : Nat -> KExpr) (uv : Level) (BB : KExpr) (aa : KExpr) \
                     (hh : @Eq (OptionType KExpr) (kdecl_type_at tenv nn uu) \
                     (@OptionType.some KExpr AA)) \
                     (hpi : @Eq KExpr (psubst ss AA) (KExpr.pi (KExpr.sort uv) BB)) \
                     (ha : whnf_acc aa) => \
                     cr1 (instantiate BB aa) (KExpr.app (KExpr.const nn uu) aa) \
                     (pi_elim (KExpr.sort uv) BB (KExpr.const nn uu) aa \
                     (@Eq.substType KExpr \
                     (fun (z : KExpr) => Red z (KExpr.const nn uu)) \
                     (psubst ss AA) (KExpr.pi (KExpr.sort uv) BB) hpi \
                     (redConst nn uu AA ss hh)) \
                     (red_sort uv aa ha)))";
        format!(
            "def candmodel_forces_app_const_whnf_acc \
             (tenv : KDeclEnv) (M : CandModel tenv) \
             (n : Name) (us : ListType Level) (A : KExpr) (s : Nat -> KExpr) \
             (u : Level) (B : KExpr) (a : KExpr) \
             (h : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) \
             (hpi : @Eq KExpr (psubst s A) (KExpr.pi (KExpr.sort u) B)) \
             (ha : whnf_acc a) : \
             whnf_acc (KExpr.app (KExpr.const n us) a) := \
             @CandModel.rec tenv {motive}{tele}{minor} M n us A s u B a h hpi ha",
            tele = CANDMODEL_MK_BINDERS,
        )
    }

    /// Rung 2's refutation vehicle, in the same absurdity idiom as rung 1's.
    ///
    /// Exhibit a `tenv` declaring a constant whose type substitutes to a
    /// sort-domained `pi`, plus one strongly normalizing argument at which the
    /// application is provably NOT strongly normalizing, and `CandModel tenv` is
    /// empty. Rung 1 could only be discharged by a non-SN bare `const`; this one
    /// admits a non-SN REDEX, which is a far larger target.
    fn candmodel_uninhabited_of_nonsn_app_src() -> String {
        "def candmodel_uninhabited_of_nonsn_app \
         (tenv : KDeclEnv) (n : Name) (us : ListType Level) (A : KExpr) \
         (s : Nat -> KExpr) (u : Level) (B : KExpr) (a : KExpr) \
         (h : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) \
         (hpi : @Eq KExpr (psubst s A) (KExpr.pi (KExpr.sort u) B)) \
         (ha : whnf_acc a) \
         (hbad : forall (C : Type), whnf_acc (KExpr.app (KExpr.const n us) a) -> C) \
         (M : CandModel tenv) (C : Type) : C := \
         hbad C (candmodel_forces_app_const_whnf_acc tenv M n us A s u B a h hpi ha)"
            .to_string()
    }

    pub(super) fn candmodel_necessary_sources() -> Vec<(String, String)> {
        vec![
            (
                "candmodel_forces_const_whnf_acc".to_string(),
                Self::candmodel_forces_const_whnf_acc_src(),
            ),
            (
                "candmodel_uninhabited_of_nonsn_const".to_string(),
                Self::candmodel_uninhabited_of_nonsn_const_src(),
            ),
            (
                "candmodel_forces_app_const_whnf_acc".to_string(),
                Self::candmodel_forces_app_const_whnf_acc_src(),
            ),
            (
                "candmodel_uninhabited_of_nonsn_app".to_string(),
                Self::candmodel_uninhabited_of_nonsn_app_src(),
            ),
        ]
    }

    /// **The EMPTY-ENVIRONMENT probe — scratch, and the reason it matters is a
    /// reduction, not a rung.**
    ///
    /// Measured 2026-09-18 from the binder list: of `CandModel`'s fifteen
    /// binders, exactly ONE mentions `tenv`, and it is `redConst`. The other
    /// thirteen laws — `pi_elim` included — are environment-independent.
    ///
    /// That collapses the vacuity question. Every `CandModel`-conditional
    /// declaration in the tree reads `forall (tenv : KDeclEnv) (M : CandModel
    /// tenv), …` (no site fixes a concrete environment), so any model at any
    /// `tenv` restricts to one at the EMPTY environment: the thirteen tenv-free
    /// laws are untouched, and `redConst` there has an unsatisfiable premise.
    /// Contrapositively, if `CandModel ⟨empty⟩` is uninhabited then so is
    /// `CandModel tenv` for EVERY `tenv`, and all the conditional declarations
    /// are vacuous at once.
    ///
    /// This probe discharges the one obligation that reduction carries: that
    /// `kdecl_type_at` at an empty `KDeclEnv` really is `none` at every name,
    /// and that `redConst`'s premise is therefore refutable there. `KDeclEnv` is
    /// `Name -> OptionType KConstSig`, a FUNCTION, so the empty environment is a
    /// constant function and the lookup should reduce by computation.
    ///
    /// It does NOT construct a model and does not claim `pi_elim` is easier
    /// here — §3g localises the telescope's content to that law, and it mentions
    /// no environment at all.
    ///
    /// `option_none_ne_some_type` rather than `opt_none_ne_some`: the latter is
    /// documented dead in `acc_wtype.rs`, whose comment asks for adoption of the
    /// live eliminator instead of a fourth orientation.
    #[cfg(test)]
    pub(super) fn candmodel_empty_env_probe_sources() -> Vec<(String, String)> {
        vec![
            (
                "kdecl_empty".to_string(),
                "def kdecl_empty : KDeclEnv := \
                 fun (_n : Name) => @OptionType.none KConstSig"
                    .to_string(),
            ),
            (
                "kdecl_empty_type_at_is_none".to_string(),
                "def kdecl_empty_type_at_is_none (n : Name) (us : ListType Level) : \
                 Eq (OptionType KExpr) (kdecl_type_at kdecl_empty n us) \
                 (@OptionType.none KExpr) := \
                 @Eq.refl (OptionType KExpr) (@OptionType.none KExpr)"
                    .to_string(),
            ),
            (
                "redconst_premise_is_refutable_at_the_empty_env".to_string(),
                "def redconst_premise_is_refutable_at_the_empty_env \
                 (n : Name) (us : ListType Level) (A : KExpr) (C : Type) \
                 (h : Eq (OptionType KExpr) (kdecl_type_at kdecl_empty n us) \
                 (@OptionType.some KExpr A)) : C := \
                 option_none_ne_some_type KExpr A C h"
                    .to_string(),
            ),
        ]
    }

    /// **THE STEP-INDEXED PROBE — scratch, and the one that matters.**
    ///
    /// §3g proves `pi_elim` is the only law that must MANUFACTURE strong
    /// normalization, and §3h localises its residual difficulty to DEPENDENCE:
    /// the honest definition needs `Red (instantiate B a)`, and `instantiate B a`
    /// is a subterm of nothing, so no `KExpr.rec` accepts it.
    ///
    /// Step-indexing sidesteps that. Recur on a `Nat` and PASS the type along:
    ///
    /// ```text
    /// RedN 0     T        e := whnf_acc e
    /// RedN (n+1) (pi A B) f := whnf_acc f AND
    ///                          (forall x, RedN n A x -> RedN n (instantiate B x) (app f x))
    /// RedN (n+1) T        e := whnf_acc e                            (T not a pi)
    /// ```
    ///
    /// The recursive call drops the INDEX, so `Nat.rec` accepts it and
    /// `instantiate B x` never has to be structurally smaller than anything.
    ///
    /// With `RedStep T e := forall n, RedN n T e`, two of the telescope's laws
    /// should follow immediately, and they are what this probe measures:
    ///
    /// * `cr1` is the `n = 0` instance, because every clause carries `whnf_acc`;
    /// * **`pi_elim`** — prove the conclusion at index `n` from the hypothesis at
    ///   `n+1`, whose body is exactly the wanted implication and whose antecedent
    ///   the second premise supplies at `n`.
    ///
    /// **MEASURED 2026-09-18: all four elaborate, 0.0 s each.** So the law the
    /// type-blind family is PROVED to fail (`pi_elim_blind_refuted_uncond`)
    /// holds at a family that is DEFINABLE, and the open question moves off
    /// `pi_elim`. The two known candidates now fail on COMPLEMENTARY halves of
    /// the Pi pair: `beta_subst_congr.rs` records the type-blind side as "the
    /// introduction rule is free; the elimination rule is the entire
    /// obstruction", and this one inverts it.
    ///
    /// **It is not a model and this probe does not claim one.** `pi_intro` is
    /// where step-indexing classically breaks: its premise is stated at `RedStep`,
    /// so it supplies `(forall m, RedN m A a) -> …`, while the `n+1` case needs
    /// the conclusion from `RedN n A a` ALONE. That residual, plus index
    /// monotonicity, is the honest remaining obligation — a different and
    /// better-understood one than "define a well-founded reducibility for
    /// dependent types".
    #[cfg(test)]
    pub(super) fn candmodel_stepindex_probe_sources() -> Vec<(String, String)> {
        let blind = "whnf_acc e0";
        let arm = |vals: &str| format!("(fun ({vals}) => {blind})");
        let redn = format!(
            "def RedN : Nat -> KExpr -> KExpr -> Type := \
             @Nat.rec (fun (_k : Nat) => KExpr -> KExpr -> Type) \
             (fun (T0 : KExpr) (e0 : KExpr) => {blind}) \
             (fun (n : Nat) (ih : KExpr -> KExpr -> Type) => \
             fun (T0 : KExpr) (e0 : KExpr) => \
             @KExpr.rec (fun (_t : KExpr) => Type) \
             {sort} {bvar} {app} {lam} \
             (fun (ty : KExpr) (bb : KExpr) (i1 : Type) (i2 : Type) => \
             AndType (whnf_acc e0) \
             (forall (x : KExpr), ih ty x -> ih (instantiate bb x) (KExpr.app e0 x))) \
             {konst} {let_} {proj} {mvar} \
             T0)",
            sort = arm("l : Level"),
            bvar = arm("i : Nat"),
            app = arm("ff : KExpr) (aa : KExpr) (i1 : Type) (i2 : Type"),
            lam = arm("ty : KExpr) (bb : KExpr) (i1 : Type) (i2 : Type"),
            konst = arm("nm : Name) (us : ListType Level"),
            let_ =
                arm("lty : KExpr) (lv : KExpr) (lb : KExpr) (i1 : Type) (i2 : Type) (i3 : Type",),
            proj = arm("ps : Name) (pidx : Nat) (sub : KExpr) (i1 : Type"),
            mvar = arm("v : Nat"),
        );
        vec![
            ("RedN".to_string(), redn),
            (
                "RedStep".to_string(),
                "def RedStep (T : KExpr) (e : KExpr) : Type := \
                 forall (n : Nat), RedN n T e"
                    .to_string(),
            ),
            (
                "redstep_cr1".to_string(),
                "def redstep_cr1 (T : KExpr) (e : KExpr) (h : RedStep T e) : \
                 whnf_acc e := h Nat.zero"
                    .to_string(),
            ),
            (
                "redstep_pi_elim".to_string(),
                "def redstep_pi_elim (A : KExpr) (B : KExpr) (f : KExpr) (a : KExpr) \
                 (hf : RedStep (KExpr.pi A B) f) (ha : RedStep A a) : \
                 RedStep (instantiate B a) (KExpr.app f a) := \
                 fun (n : Nat) => \
                 AndType.right (whnf_acc f) \
                 (forall (x : KExpr), RedN n A x -> \
                 RedN n (instantiate B x) (KExpr.app f x)) \
                 (hf (Nat.succ n)) a (ha n)"
                    .to_string(),
            ),
        ]
    }

    /// **What `pi_intro` COSTS at the step-indexed family — scratch.**
    ///
    /// `redstep_pi_elim` discharges the hard half of the Pi pair. This measures
    /// the other half, and it measures it by PROVING a strengthened form rather
    /// than by writing a term that fails: a failing term tells you only that one
    /// spelling did not work, while a proof under an explicit extra premise says
    /// exactly what the telescope does not hand you.
    ///
    /// `redstep_pi_intro_per_index` takes TWO things the real field does not
    /// carry:
    ///
    /// * `whnf_acc f` outright — the field gives no `whnf_acc` for `f`, and at
    ///   index 0 there is nothing else to return, since `RedN 0 T e` IS
    ///   `whnf_acc e`;
    /// * the pointwise premise PER INDEX (`forall n x, RedN n A x -> …`), where
    ///   the field states it at `RedStep`, i.e. `(forall m, RedN m A x) -> …`.
    ///
    /// Given those two it goes through by `Nat.rec` on the index. So the gap is
    /// not that `pi_intro` is false here; it is that the field's premise is
    /// quantified at the WRONG PLACE — outside the index rather than inside it —
    /// and nothing recovers a universally quantified antecedent from one index.
    /// That is the classical step-indexing mismatch, named precisely.
    ///
    /// `redstep_red_sort` is registered beside it as a control: a law that DOES
    /// go through unchanged, by the same `Nat.rec`, so a failure of the first is
    /// not read as the technique failing.
    #[cfg(test)]
    pub(super) fn candmodel_stepindex_pi_intro_sources() -> Vec<(String, String)> {
        vec![
            (
                "redstep_red_sort".to_string(),
                "def redstep_red_sort (nn : Level) (e : KExpr) (h : whnf_acc e) : \
                 RedStep (KExpr.sort nn) e := \
                 fun (n : Nat) => \
                 @Nat.rec (fun (k : Nat) => RedN k (KExpr.sort nn) e) h \
                 (fun (k : Nat) (_ih : RedN k (KExpr.sort nn) e) => h) n"
                    .to_string(),
            ),
            (
                "redstep_pi_intro_per_index".to_string(),
                "def redstep_pi_intro_per_index (A : KExpr) (B : KExpr) (f : KExpr) \
                 (hw : whnf_acc f) \
                 (hp : forall (k : Nat) (x : KExpr), RedN k A x -> \
                 RedN k (instantiate B x) (KExpr.app f x)) : \
                 RedStep (KExpr.pi A B) f := \
                 fun (n : Nat) => \
                 @Nat.rec (fun (k : Nat) => RedN k (KExpr.pi A B) f) hw \
                 (fun (k : Nat) (_ih : RedN k (KExpr.pi A B) f) => \
                 @AndType.intro (whnf_acc f) \
                 (forall (x : KExpr), RedN k A x -> \
                 RedN k (instantiate B x) (KExpr.app f x)) hw (hp k)) n"
                    .to_string(),
            ),
        ]
    }

    /// **`cr2` at the step-indexed family — scratch.**
    ///
    /// The first law here that needs a genuine TWO-LEVEL induction, which is why
    /// it is worth measuring rather than assuming. `cr1`, `red_sort` and
    /// `pi_elim` are each a projection or a one-line `Nat.rec`; this one is
    /// `Nat.rec` on the INDEX with a `KExpr.rec` on the TYPE inside it, and the
    /// `pi` arm consumes the outer hypothesis at a DIFFERENT type
    /// (`instantiate bb z`) and a different pair of terms than it was invoked
    /// at.
    ///
    /// That is only possible because the outer motive quantifies the type:
    ///
    /// ```text
    /// fun k => forall T x y, RedN k T x -> whnf_step x y -> RedN k T y
    /// ```
    ///
    /// A motive that fixed `T` would give an induction hypothesis useless at the
    /// `pi` arm, which is exactly the shape that makes this a real check on the
    /// step-indexed definition rather than a restatement.
    ///
    /// Eight arms are `whnf_acc_step` verbatim — at a non-`pi` type every clause
    /// of `RedN` IS `whnf_acc`, at every index. The `pi` arm rebuilds the pair:
    /// left by `whnf_acc_step` again, right by transporting the pointwise
    /// function along `whnfStep_app_left` under the outer hypothesis at index
    /// `k`.
    #[cfg(test)]
    pub(super) fn candmodel_stepindex_cr2_sources() -> Vec<(String, String)> {
        let motive = "fun (kk : Nat) => forall (T : KExpr) (x : KExpr) (y : KExpr), \
                      RedN kk T x -> whnf_step x y -> RedN kk T y";
        // The inner KExpr.rec's motive, at a bound type variable.
        let inner = "fun (T0 : KExpr) => RedN (Nat.succ k) T0 x -> whnf_step x y -> \
                     RedN (Nat.succ k) T0 y";
        let step_arm = "fun (h : whnf_acc x) (st : whnf_step x y) => whnf_acc_step x y h st";
        let ih = |t: &str| {
            format!("RedN (Nat.succ k) {t} x -> whnf_step x y -> RedN (Nat.succ k) {t} y")
        };
        let arm = |vals: &str, subs: &[&str]| {
            let ihs: String = subs
                .iter()
                .enumerate()
                .map(|(n, t)| format!(" (j{n} : {})", ih(t)))
                .collect();
            format!("(fun ({vals}){ihs} => {step_arm})")
        };
        let pi_arm = format!(
            "(fun (ty : KExpr) (bb : KExpr) (j0 : {ihty}) (j1 : {ihbb}) => \
             fun (h : RedN (Nat.succ k) (KExpr.pi ty bb) x) (st : whnf_step x y) => \
             @AndType.intro (whnf_acc y) \
             (forall (z : KExpr), RedN k ty z -> \
             RedN k (instantiate bb z) (KExpr.app y z)) \
             (whnf_acc_step x y \
             (AndType.left (whnf_acc x) \
             (forall (z : KExpr), RedN k ty z -> \
             RedN k (instantiate bb z) (KExpr.app x z)) h) st) \
             (fun (z : KExpr) (hz : RedN k ty z) => \
             ih (instantiate bb z) (KExpr.app x z) (KExpr.app y z) \
             (AndType.right (whnf_acc x) \
             (forall (w : KExpr), RedN k ty w -> \
             RedN k (instantiate bb w) (KExpr.app x w)) h z hz) \
             (whnfStep_app_left x y z st)))",
            ihty = ih("ty"),
            ihbb = ih("bb"),
        );
        let body = format!(
            "@Nat.rec ({motive}) \
             (fun (T : KExpr) (x : KExpr) (y : KExpr) (h : whnf_acc x) \
             (st : whnf_step x y) => whnf_acc_step x y h st) \
             (fun (k : Nat) (ih : forall (T : KExpr) (x : KExpr) (y : KExpr), \
             RedN k T x -> whnf_step x y -> RedN k T y) => \
             fun (T : KExpr) (x : KExpr) (y : KExpr) => \
             @KExpr.rec ({inner}) \
             {sort} {bvar} {app} {lam} {pi_arm} {konst} {let_} {proj} {mvar} \
             T) n TT e e2 (h n) st",
            sort = arm("l : Level", &[]),
            bvar = arm("i : Nat", &[]),
            app = arm("ff : KExpr) (aa : KExpr", &["ff", "aa"]),
            lam = arm("lty : KExpr) (lb : KExpr", &["lty", "lb"]),
            konst = arm("nm : Name) (us : ListType Level", &[]),
            let_ = arm(
                "zty : KExpr) (zv : KExpr) (zb : KExpr",
                &["zty", "zv", "zb"],
            ),
            proj = arm("ps : Name) (pidx : Nat) (sub : KExpr", &["sub"]),
            mvar = arm("v : Nat", &[]),
        );
        vec![(
            "redstep_cr2".to_string(),
            format!(
                "def redstep_cr2 (TT : KExpr) (e : KExpr) (e2 : KExpr) \
                 (h : RedStep TT e) (st : whnf_step e e2) : RedStep TT e2 := \
                 fun (n : Nat) => {body}"
            ),
        )]
    }

    /// **`redTypeStep` REFUTED at the step-indexed family — scratch.**
    ///
    /// The prediction §3k derives, made checkable. A family that decides
    /// reducibility by the type's HEAD CONSTRUCTOR cannot be invariant under a
    /// step in the type, because a step can move the head. Here it moves it
    /// across the `pi` boundary, which is the boundary that matters: at a `pi`
    /// the clause is an `AndType` carrying a pointwise condition, and everywhere
    /// else it is bare `whnf_acc`.
    ///
    /// The witness is a beta redex whose contractum is a `pi`:
    ///
    /// ```text
    /// T  := app (lam (sort 0) (pi (sort 0) (sort 0))) (sort 0)     -- head is `app`
    /// T2 := pi (sort 0) (sort 0)                                   -- head is `pi`
    /// whnf_step T T2                                               -- one beta step
    /// ```
    ///
    /// At `e := OMEGA_LAM` the two sides come apart:
    ///
    /// * `RedStep T OMEGA_LAM` is INHABITED — `T` is `app`-headed, so every
    ///   clause of `RedN` at it is `whnf_acc OMEGA_LAM`, which holds;
    /// * `RedStep T2 OMEGA_LAM` is EMPTY — at index 1 it demands
    ///   `forall x, whnf_acc x -> whnf_acc (app OMEGA_LAM x)`, and instantiating
    ///   at `OMEGA_LAM` itself yields `whnf_acc (app OMEGA_LAM OMEGA_LAM)`, which
    ///   `self_app_loop_not_whnf_acc` refutes.
    ///
    /// So the law's FORWARD direction carries an inhabited thing to an empty one.
    /// This is a refutation in the same sense as `pi_elim_blind_refuted_uncond`:
    /// assume the field and derive `C` for arbitrary `C`, with no side condition
    /// and no bogus term.
    ///
    /// **What it costs, stated with it.** `redTypeStep` is one of the EIGHT laws
    /// §3d measures as holding exactly at the type-BLIND family — it holds there
    /// precisely because that family ignores the type. So this is the second
    /// half of the trade §3k names: type-awareness buys `pi_elim` and costs
    /// `redTypeStep`, and the two candidates fail on disjoint laws.
    #[cfg(test)]
    pub(super) fn candmodel_stepindex_typestep_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let pi = format!("(KExpr.pi {s0} {s0})");
        let t = format!("(KExpr.app (KExpr.lam {s0} {pi}) {s0})");
        let om = "(KExpr.lam (KExpr.bvar Nat.zero) \
                  (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)))";
        // `RedStep T OMEGA_LAM`: T is `app`-headed, so every index gives
        // `whnf_acc OMEGA_LAM`. Needs a `Nat.rec` because `RedN n` does not
        // reduce at a variable index -- the same shape `redstep_red_sort` uses.
        let red_t = format!(
            "(fun (n : Nat) => @Nat.rec (fun (k : Nat) => RedN k {t} {om}) \
             whnf_acc_omega_lam_uncond \
             (fun (k : Nat) (_ih : RedN k {t} {om}) => whnf_acc_omega_lam_uncond) n)"
        );
        let pointwise = format!(
            "(forall (x : KExpr), RedN Nat.zero {s0} x -> \
             RedN Nat.zero {s0} (KExpr.app {om} x))"
        );
        vec![(
            "redstep_redTypeStep_refuted".to_string(),
            format!(
                "def redstep_redTypeStep_refuted (C : Type) \
                 (law : forall (T : KExpr) (T2 : KExpr) (e : KExpr), \
                 whnf_step T T2 -> \
                 AndType (RedStep T e -> RedStep T2 e) (RedStep T2 e -> RedStep T e)) : C := \
                 self_app_loop_not_whnf_acc {om} omega_self_step C \
                 (AndType.right (whnf_acc {om}) {pointwise} \
                 (AndType.left (RedStep {t} {om} -> RedStep {pi} {om}) \
                 (RedStep {pi} {om} -> RedStep {t} {om}) \
                 (law {t} {pi} {om} \
                 (whnf_step.beta {t} {pi} \
                 (beta_reduces.beta {s0} {pi} {s0}))) \
                 {red_t} (Nat.succ Nat.zero)) \
                 {om} whnf_acc_omega_lam_uncond)"
            ),
        )]
    }

    /// **The step index is LOAD-BEARING, not decoration — scratch.**
    ///
    /// Worth pinning because the reader's first instinct at `RedStep T e :=
    /// forall n, RedN n T e` is that the index cancels out, and if it did the
    /// whole construction would be the type-blind family wearing a disguise —
    /// where `pi_elim` is PROVED FALSE. So `pi_elim` holding at `RedStep` already
    /// implies the index does something; this exhibits WHAT, concretely.
    ///
    /// At `T := pi (sort 0) (sort 0)` and `e := OMEGA_LAM` the two lowest
    /// indices disagree:
    ///
    /// * `RedN 0 T OMEGA_LAM` is `whnf_acc OMEGA_LAM` — INHABITED, since the
    ///   zero clause ignores the type entirely;
    /// * `RedN 1 T OMEGA_LAM` is `AndType (whnf_acc OMEGA_LAM) (forall x,
    ///   whnf_acc x -> whnf_acc (app OMEGA_LAM x))` — EMPTY, by the same
    ///   `self_app_loop_not_whnf_acc` route the `redTypeStep` refutation uses.
    ///
    /// So `RedN` is NOT upward closed in the index, with a witness. A corollary
    /// worth stating: `RedN` cannot be closed in BOTH directions, because a
    /// relation closed both ways is index-independent, and an index-independent
    /// `RedN` makes `RedStep` equal to `RedN 0`, which IS `whnf_acc` — the
    /// family `pi_elim_blind_refuted_uncond` refutes. The index is where
    /// `pi_elim` is bought.
    #[cfg(test)]
    pub(super) fn candmodel_stepindex_loadbearing_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let pi = format!("(KExpr.pi {s0} {s0})");
        let om = "(KExpr.lam (KExpr.bvar Nat.zero) \
                  (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)))";
        let pointwise = format!(
            "(forall (x : KExpr), RedN Nat.zero {s0} x -> \
             RedN Nat.zero {s0} (KExpr.app {om} x))"
        );
        vec![
            (
                "redn_index_zero_is_inhabited_at_omega".to_string(),
                format!(
                    "def redn_index_zero_is_inhabited_at_omega : \
                     RedN Nat.zero {pi} {om} := whnf_acc_omega_lam_uncond"
                ),
            ),
            (
                "redn_index_one_is_empty_at_omega".to_string(),
                format!(
                    "def redn_index_one_is_empty_at_omega (C : Type) \
                     (h : RedN (Nat.succ Nat.zero) {pi} {om}) : C := \
                     self_app_loop_not_whnf_acc {om} omega_self_step C \
                     (AndType.right (whnf_acc {om}) {pointwise} h \
                     {om} whnf_acc_omega_lam_uncond)"
                ),
            ),
        ]
    }

    /// Registered from `bundles.rs` after `add_beta_subst_congr`, which is after
    /// `add_dependent_sn_richmodel` — the stage that declares `CandModel`
    /// itself. Nothing here needs the substitution lemmas; the position is
    /// chosen so the two `CandModel`-facing stages stay adjacent.
    pub(super) fn add_candmodel_necessary(&mut self) -> Result<(), SpecError> {
        for (_n, src) in Self::candmodel_necessary_sources() {
            self.add_recursive_def(&src, "CandModel necessary condition")?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_necessary_tests.rs"]
mod tests;
