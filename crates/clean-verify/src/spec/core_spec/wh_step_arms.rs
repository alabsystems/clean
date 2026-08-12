// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The arms of step monotonicity, and the boundary contradiction.
//!
//! ## What is here
//!
//! Step monotonicity recurses on the expression. Seven of its nine arms are
//! trivial — the step is budget-independent there — and this module holds the
//! two that are not, plus the machinery the harder one needs.
//!
//! * `wh_step_mono_proj_arm` — projection. `opt_proj_lift` never mentions the
//!   pre-pass, so this is a convoy plus one congruence.
//! * `wh_step_mono_app_some_cf` — application whose head-reduct is already
//!   `some`. The step then never consults the pre-pass at all.
//! * `no_name_cf_none_transfer` — application with a `none` head-reduct under a
//!   head that is not a constant. ι stops at level one, so the premise is
//!   absurd, except at a lambda where β makes premise and goal identical. Note
//!   its target head-reduct is ARBITRARY, which is what lets it apply without
//!   knowing the step at the second budget — the thing that is not available.
//! * `step_none_implies_iota_none` — the bridge from "the step found nothing" to
//!   "ι found nothing". The boundary argument has a hypothesis about the step
//!   and must contradict a conclusion about ι.
//! * `iota_case_a_major_agrees` — when the major-premise index lies strictly
//!   inside `f`'s own arguments, `app f a` and `f` read the SAME element there.
//! * `iota_case_a_contradiction` / `iota_case_b_cf_stable` — the two halves of
//!   the boundary argument, each showing the head-reduct cannot flip.
//!
//! ## Both universes, from one source
//!
//! The two boundary lemmas conclude at a parameter `C`, and this kernel is
//! **non-cumulative**: `is_le` falls back to `is_def_eq` unless `cumulative`,
//! `Type` parses to `Sort 1`, and the spec's `Eq` is `Prop`-valued. A `C : Type`
//! conclusion therefore cannot be instantiated at an equation — which is what
//! every caller in the `app` arm has. So each is emitted at BOTH universes from
//! one source, differing only in the binder and in which absurdity helper it
//! calls (`option_none_ne_some_type` takes `C : Type`, the plain one
//! `R : Prop`; argument orders are identical).
//!
//! That is the same pairing `iota_reduct_some_inv` / `..._type` already uses,
//! and the same reason: a CPS eliminator fixed at one universe is unusable by
//! callers living in the other.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The two non-trivial arms, the step/ι bridge, and the boundary.
    pub(super) fn add_wh_step_arms(&mut self) -> Result<(), SpecError> {
        self.add_simple_arms()?;
        self.add_iota_bridge()?;
        self.add_boundary_cases()?;
        Ok(())
    }

    /// The arms that need no ι reasoning at all.
    fn add_simple_arms(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_WH_STEP_MONO_PROJ_ARM,
            "wh_step_mono_proj_arm: the projection arm. opt_proj_lift never mentions the pre-pass, so this is a convoy on the subterm's step plus one congruence: a none reduct makes the premise absurd, and a some reduct is carried by the induction hypothesis. No iota reasoning is involved, which is why this arm is easy where the application arm is not. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH_STEP_MONO_APP_SOME_CF,
            "wh_step_mono_app_some_cf: the application arm when the head-reduct is already some. The step then takes opt_app_ilift's congruence branch, which does not consult the pre-pass, so raising the budget cannot change the answer. A chain of rewrites, no induction. The hard half is the none case, where iota is reachable. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_NO_NAME_CF_NONE_TRANSFER,
            "no_name_cf_none_transfer: a none head-reduct under a head that is NOT a constant. Nine arms: at a lambda, beta makes premise and goal the same term, since reduce_app_head_red_wh ignores the head-reduct there; at a bare constant the branch hypothesis is contradictory; everywhere else iota stops at level one and the premise is absurd. \nIts TARGET head-reduct is arbitrary, which is the point: the caller does not know the step at the second budget, and this lemma does not ask. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// From "the step found nothing" to "ι found nothing".
    fn add_iota_bridge(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_STEP_NONE_IMPLIES_IOTA_NONE,
            "step_none_implies_iota_none: if the step on a CONST-HEADED term found nothing, then in particular iota found nothing on it. Needed because the boundary argument holds a hypothesis about the STEP and must contradict a conclusion about IOTA. \nNine arms. The seven non-const, non-app shapes carry no head name, so the first hypothesis is contradictory. A bare constant has an empty argument list, so the chain dies for want of a major premise — reached by a convoy on the metadata lookup, taking the level-two exit when it is absent and the level-three exit when it is present, the latter's bound supplied by le_zero_n since an empty spine has length zero. The app arm convoys on the head's own step: a some reduct contradicts the hypothesis, and a none reduct makes the step BE the iota call. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The boundary argument: the head-reduct cannot flip.
    ///
    /// Each case is emitted at BOTH universes from one source. The kernel is
    /// non-cumulative, so a `C : Type` conclusion cannot be instantiated at an
    /// equation — and the `app` arm's goal is an equation.
    fn add_boundary_cases(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_IOTA_CASE_A_MAJOR_AGREES,
            "iota_case_a_major_agrees: when the major-premise index lies STRICTLY inside f's own \
             argument list, the element (app f a) reads there is the element f reads there. The two \
             lists differ only by one argument appended past the index. \
             \
             No induction: list_head_drop_append_some_inv (iota_core.rs) states exactly this, and \
             its strict guard Le (succ k) (list_length xs) IS the Case A hypothesis. That \
             strictness is what separates the cases — at k = length xs the appended argument IS \
             the major and the shorter lookup is none, which is Case B. The transport is one \
             Eq.cong along kapp_args_app. DerivedProved, zero axiom_deps.",
        )?;

        for (suffix, univ, helper) in [
            ("_type", "Type", "option_none_ne_some_type"),
            ("", "Prop", "option_none_ne_some"),
        ] {
            for (base, src, what) in [
                (
                    "iota_case_a_contradiction",
                    SRC_IOTA_CASE_A_CONTRADICTION,
                    "iota fired on (app f a) and the major premise lies strictly inside f's own \
                     arguments, so iota would have fired on f too — contradicting the assumption \
                     that the step on f found nothing",
                ),
                (
                    "iota_case_b_cf_stable",
                    SRC_IOTA_CASE_B_CF_STABLE,
                    "the spine f is one argument short of its major premise, so its step does not \
                     depend on the pre-pass at all and cannot be none at one budget and some at \
                     another",
                ),
            ] {
                let s = src
                    .replace(&format!("def {base} "), &format!("def {base}{suffix} "))
                    .replace("(C : Type)", &format!("(C : {univ})"))
                    .replace("option_none_ne_some_type", helper);
                debug_assert!(Self::balanced(&s), "{base}{suffix} parens");
                self.add_recursive_def(
                    &s,
                    &format!(
                        "{base}{suffix}: a boundary contradiction — {what}. Concluding at \
                         C : {univ}. \
                         \
                         Emitted at both universes from ONE source because this kernel is \
                         non-cumulative: Type is Sort 1, the spec's Eq is Prop-valued, and a \
                         C : Type conclusion cannot be instantiated at an equation. The app arm's \
                         goal IS an equation, so the Prop variant is the one it uses; the Type \
                         variant serves callers concluding in Empty or a relation. \
                         DerivedProved, zero axiom_deps."
                    ),
                )?;
            }
        }
        Ok(())
    }
}

const SRC_WH_STEP_MONO_PROJ_ARM: &str = "def wh_step_mono_proj_arm (wh1 : KExpr -> OptionType KExpr) (wh2 : KExpr -> OptionType KExpr) (s : Name) (i : Nat) (sub : KExpr) (x0 : KExpr) (ihsub : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 sub) (OptionType.some KExpr y) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 sub) (OptionType.some KExpr y)) : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.proj s i sub)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.proj s i sub)) (OptionType.some KExpr x0) := fun (hp : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.proj s i sub)) (OptionType.some KExpr x0)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 sub) o -> Eq (OptionType KExpr) (opt_proj_lift s i o) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.proj s i sub)) (OptionType.some KExpr x0)) (fun (_hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 sub) (OptionType.none KExpr)) (h2 : Eq (OptionType KExpr) (OptionType.none KExpr) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.proj s i sub)) (OptionType.some KExpr x0)) h2) (fun (sub2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 sub) (OptionType.some KExpr sub2)) (h2 : Eq (OptionType KExpr) (OptionType.some KExpr (KExpr.proj s i sub2)) (OptionType.some KExpr x0)) => Eq.trans (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.proj s i sub)) (OptionType.some KExpr (KExpr.proj s i sub2)) (OptionType.some KExpr x0) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (o : OptionType KExpr) => opt_proj_lift s i o) (reduce_once_red_wh the_red_env wh2 sub) (OptionType.some KExpr sub2) (ihsub sub2 hq)) h2) (reduce_once_red_wh the_red_env wh1 sub) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 sub)) hp";

const SRC_WH_STEP_MONO_APP_SOME_CF: &str = "def wh_step_mono_app_some_cf (wh1 : KExpr -> OptionType KExpr) (wh2 : KExpr -> OptionType KExpr) (a : KExpr) (f : KExpr) (f2 : KExpr) (x0 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.some KExpr f2)) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.some KExpr y) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr y)) : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0) := fun (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0)) => Eq.trans (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (reduce_app_head_red_wh the_red_env wh2 a f (OptionType.some KExpr f2)) (OptionType.some KExpr x0) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (z : OptionType KExpr) => reduce_app_head_red_wh the_red_env wh2 a f z) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr f2) (ihf f2 hq)) (Eq.trans (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a f (OptionType.some KExpr f2)) (reduce_app_head_red_wh the_red_env wh1 a f (OptionType.some KExpr f2)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a f (OptionType.some KExpr f2)) (reduce_app_head_red_wh the_red_env wh2 a f (OptionType.some KExpr f2)) (reduce_app_head_some_cf_wh_indep wh1 wh2 a f2 f)) (Eq.trans (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a f (OptionType.some KExpr f2)) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (z : OptionType KExpr) => reduce_app_head_red_wh the_red_env wh1 a f z) (OptionType.some KExpr f2) (reduce_once_red_wh the_red_env wh1 f) (Eq.symm (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.some KExpr f2) hq)) h))";

const SRC_NO_NAME_CF_NONE_TRANSFER: &str = "def no_name_cf_none_transfer (wh1 : KExpr -> OptionType KExpr) (wh2 : KExpr -> OptionType KExpr) (a : KExpr) (x0 : KExpr) (cf2 : OptionType KExpr) (f : KExpr) : (Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a f (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a f cf2) (OptionType.some KExpr x0)) := KExpr.rec (fun (x : KExpr) => (Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a x (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a x cf2) (OptionType.some KExpr x0))) (fun (n : Level) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.sort n))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.sort n) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.sort n) cf2) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.sort n) a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.sort n) a)) (OptionType.none KExpr) (iota_reduct_whc_none_of_no_head (red_rec the_red_env) wh1 (KExpr.app (KExpr.sort n) a) h)) hp)) (fun (i : Nat) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.bvar i))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.bvar i) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.bvar i) cf2) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.bvar i) a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.bvar i) a)) (OptionType.none KExpr) (iota_reduct_whc_none_of_no_head (red_rec the_red_env) wh1 (KExpr.app (KExpr.bvar i) a) h)) hp)) (fun (g : KExpr) (b : KExpr) (_c1 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn g)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a g (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a g cf2) (OptionType.some KExpr x0))) (_c2 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a b (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a b cf2) (OptionType.some KExpr x0))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g b))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.app g b) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.app g b) cf2) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.app g b) a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.app g b) a)) (OptionType.none KExpr) (iota_reduct_whc_none_of_no_head (red_rec the_red_env) wh1 (KExpr.app (KExpr.app g b) a) h)) hp)) (fun (ty : KExpr) (b : KExpr) (_c1 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a ty (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a ty cf2) (OptionType.some KExpr x0))) (_c2 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a b (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a b cf2) (OptionType.some KExpr x0))) (_h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty b))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.lam ty b) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => hp) (fun (ty : KExpr) (b : KExpr) (_c1 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a ty (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a ty cf2) (OptionType.some KExpr x0))) (_c2 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a b (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a b cf2) (OptionType.some KExpr x0))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi ty b))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.pi ty b) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.pi ty b) cf2) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.pi ty b) a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.pi ty b) a)) (OptionType.none KExpr) (iota_reduct_whc_none_of_no_head (red_rec the_red_env) wh1 (KExpr.app (KExpr.pi ty b) a) h)) hp)) (fun (cn : Name) (us : ListType Level) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const cn us))) (OptionType.none Name)) (_hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.const cn us) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some Name cn (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.const cn us) cf2) (OptionType.some KExpr x0)) (Eq.symm (OptionType Name) (OptionType.some Name cn) (OptionType.none Name) h)) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a ty (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a ty cf2) (OptionType.some KExpr x0))) (_c2 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a v (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a v cf2) (OptionType.some KExpr x0))) (_c3 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a b (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a b cf2) (OptionType.some KExpr x0))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty v b))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.let_ ty v b) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.let_ ty v b) cf2) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.let_ ty v b) a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.let_ ty v b) a)) (OptionType.none KExpr) (iota_reduct_whc_none_of_no_head (red_rec the_red_env) wh1 (KExpr.app (KExpr.let_ ty v b) a) h)) hp)) (fun (s : Name) (i : Nat) (sub : KExpr) (_cs : (Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.none Name) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a sub (OptionType.none KExpr)) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a sub cf2) (OptionType.some KExpr x0))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.proj s i sub) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.proj s i sub) cf2) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.proj s i sub) a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.proj s i sub) a)) (OptionType.none KExpr) (iota_reduct_whc_none_of_no_head (red_rec the_red_env) wh1 (KExpr.app (KExpr.proj s i sub) a) h)) hp)) (fun (v : Nat) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lit v))) (OptionType.none Name)) (hp : Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a (KExpr.lit v) (OptionType.none KExpr)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh2 a (KExpr.lit v) cf2) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.lit v) a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app (KExpr.lit v) a)) (OptionType.none KExpr) (iota_reduct_whc_none_of_no_head (red_rec the_red_env) wh1 (KExpr.app (KExpr.lit v) a) h)) hp)) f";

const SRC_STEP_NONE_IMPLIES_IOTA_NONE: &str = "def step_none_implies_iota_none (wh : KExpr -> OptionType KExpr) (nm : Name) (f : KExpr) : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh f) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh f) (OptionType.none KExpr) := KExpr.rec (fun (x : KExpr) => (Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh x) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh x) (OptionType.none KExpr))) (fun (n : Level) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.sort n))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.sort n)) (OptionType.none KExpr)) => option_none_ne_some Name nm (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.sort n)) (OptionType.none KExpr)) h) (fun (i : Nat) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.bvar i))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.bvar i)) (OptionType.none KExpr)) => option_none_ne_some Name nm (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.bvar i)) (OptionType.none KExpr)) h) (fun (g : KExpr) (b : KExpr) (_ihg : (Eq (OptionType Name) (kexpr_const_name (kapp_fn g)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh g) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh g) (OptionType.none KExpr))) (_ihb : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh b) (OptionType.none KExpr))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app g b))) (OptionType.some Name nm)) (hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app g b)) (OptionType.none KExpr)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh g) o -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app g b)) (OptionType.none KExpr)) (fun (hcf : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh g) (OptionType.none KExpr)) => Eq.trans (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app g b)) (opt_app_ilift_wh the_red_env wh g b (reduce_once_red_wh the_red_env wh g)) (OptionType.none KExpr) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (z : OptionType KExpr) => opt_app_ilift_wh the_red_env wh g b z) (OptionType.none KExpr) (reduce_once_red_wh the_red_env wh g) (Eq.symm (OptionType KExpr) (reduce_once_red_wh the_red_env wh g) (OptionType.none KExpr) hcf)) (Eq.trans (OptionType KExpr) (opt_app_ilift_wh the_red_env wh g b (reduce_once_red_wh the_red_env wh g)) (reduce_app_head_red_wh the_red_env wh b g (reduce_once_red_wh the_red_env wh g)) (OptionType.none KExpr) (Eq.symm (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh b g (reduce_once_red_wh the_red_env wh g)) (opt_app_ilift_wh the_red_env wh g b (reduce_once_red_wh the_red_env wh g)) (reduce_app_head_const_is_ilift wh b (reduce_once_red_wh the_red_env wh g) nm g h)) hs)) (fun (g2 : KExpr) (hcf : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh g) (OptionType.some KExpr g2)) => option_none_ne_some KExpr (KExpr.app g2 b) (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.app g b)) (OptionType.none KExpr)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (reduce_app_head_red_wh the_red_env wh b g (reduce_once_red_wh the_red_env wh g)) (OptionType.some KExpr (KExpr.app g2 b)) (Eq.symm (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh b g (reduce_once_red_wh the_red_env wh g)) (OptionType.none KExpr) hs) (Eq.trans (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh b g (reduce_once_red_wh the_red_env wh g)) (opt_app_ilift_wh the_red_env wh g b (reduce_once_red_wh the_red_env wh g)) (OptionType.some KExpr (KExpr.app g2 b)) (reduce_app_head_const_is_ilift wh b (reduce_once_red_wh the_red_env wh g) nm g h) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (z : OptionType KExpr) => opt_app_ilift_wh the_red_env wh g b z) (reduce_once_red_wh the_red_env wh g) (OptionType.some KExpr g2) hcf)))) (reduce_once_red_wh the_red_env wh g) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh g))) (fun (ty : KExpr) (b : KExpr) (_c1 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh ty) (OptionType.none KExpr))) (_c2 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh b) (OptionType.none KExpr))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam ty b))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lam ty b)) (OptionType.none KExpr)) => option_none_ne_some Name nm (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.lam ty b)) (OptionType.none KExpr)) h) (fun (ty : KExpr) (b : KExpr) (_c1 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh ty) (OptionType.none KExpr))) (_c2 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh b) (OptionType.none KExpr))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi ty b))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.pi ty b)) (OptionType.none KExpr)) => option_none_ne_some Name nm (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.pi ty b)) (OptionType.none KExpr)) h) (fun (cn : Name) (us : ListType Level) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.const cn us))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.const cn us)) (OptionType.none KExpr)) => OptionType.rec RecMeta (fun (om : OptionType RecMeta) => Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) om -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.const cn us)) (OptionType.none KExpr)) (fun (hrm : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.none RecMeta)) => iota_reduct_whc_none_of_no_recmeta (red_rec the_red_env) wh (KExpr.const cn us) nm h hrm) (fun (meta : RecMeta) (hrm : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta)) => iota_reduct_whc_none_of_no_major (red_rec the_red_env) wh (KExpr.const cn us) nm meta h hrm (list_head_drop_none_of_le (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.const cn us)) (le_zero_n (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))))) (recmeta_for (red_rec the_red_env) nm) (Eq.refl (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm))) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn ty)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh ty) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh ty) (OptionType.none KExpr))) (_c2 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh v) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh v) (OptionType.none KExpr))) (_c3 : (Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh b) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh b) (OptionType.none KExpr))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ ty v b))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.let_ ty v b)) (OptionType.none KExpr)) => option_none_ne_some Name nm (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.let_ ty v b)) (OptionType.none KExpr)) h) (fun (s : Name) (i : Nat) (sub : KExpr) (_cs : (Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name nm) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh sub) (OptionType.none KExpr) -> Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh sub) (OptionType.none KExpr))) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj s i sub))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.proj s i sub)) (OptionType.none KExpr)) => option_none_ne_some Name nm (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.proj s i sub)) (OptionType.none KExpr)) h) (fun (v : Nat) (h : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lit v))) (OptionType.some Name nm)) (_hs : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.lit v)) (OptionType.none KExpr)) => option_none_ne_some Name nm (Eq (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh (KExpr.lit v)) (OptionType.none KExpr)) h) f";

const SRC_IOTA_CASE_A_MAJOR_AGREES: &str = "def iota_case_a_major_agrees (f : KExpr) (a : KExpr) (meta : RecMeta) (major : KExpr) (hlt : Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (list_length (kapp_args f))) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f))) (OptionType.some KExpr major) := list_head_drop_append_some_inv (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args f) a major hlt (Eq.trans (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))))) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major) (Eq.cong (ListType KExpr) (OptionType KExpr) (fun (L : ListType KExpr) => list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) L)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args (KExpr.app f a)) (Eq.symm (ListType KExpr) (kapp_args (KExpr.app f a)) (list_append (kapp_args f) (ListType.cons KExpr a (ListType.nil KExpr))) (kapp_args_app f a))) h3)";

const SRC_IOTA_CASE_A_CONTRADICTION: &str = "def iota_case_a_contradiction (wh : KExpr -> OptionType KExpr) (f : KExpr) (a : KExpr) (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule) (C : Type) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) (h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) recname) (OptionType.some RecMeta meta)) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) (hw : Eq (OptionType KExpr) (wh major) (OptionType.some KExpr wmajor)) (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cname)) (h5 : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) recname cname) (OptionType.some RecRule rule)) (hlt : Le (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (list_length (kapp_args f))) (hnone : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh f) (OptionType.none KExpr)) : C := option_none_ne_some_type KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args wmajor)) (recrule_num_fields rule)) (kapp_args wmajor)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule)))) C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (iota_reduct_whc (red_rec the_red_env) wh f) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args f)) (apply_spine (list_drop (Nat.sub (list_length (kapp_args wmajor)) (recrule_num_fields rule)) (kapp_args wmajor)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args f)) (recrule_rhs rule))))) (Eq.symm (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh f) (OptionType.none KExpr) (step_none_implies_iota_none wh recname f h1 hnone)) (iota_reduct_whc_some_of_facts (red_rec the_red_env) wh f recname meta major wmajor cname rule h1 h2 (iota_case_a_major_agrees f a meta major hlt h3) hw h4 h5))";

const SRC_IOTA_CASE_B_CF_STABLE: &str = "def iota_case_b_cf_stable (wh1 : KExpr -> OptionType KExpr) (wh2 : KExpr -> OptionType KExpr) (nm : Name) (meta : RecMeta) (f : KExpr) (f2 : KExpr) (C : Type) (hrm : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) (OptionType.some RecMeta meta)) (hhf : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) (hle : Le (list_length (kapp_args f)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (hnone : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr)) (hsome : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr f2)) : C := option_none_ne_some_type KExpr f2 C (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr f2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (reduce_once_red_wh the_red_env wh1 f) (reduce_once_red_wh the_red_env wh2 f) (Eq.symm (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr) hnone) (under_applied_step_congr wh1 wh2 nm meta hrm f hhf hle)) hsome)";

#[cfg(test)]
mod tests {
    use super::*;

    /// Every source must PARSE. This is the cheap gate: parsing one
    /// declaration costs microseconds, while discovering the same error through
    /// a specification build costs ~27 minutes. Paren balance is necessary and
    /// nowhere near sufficient — a term missing its `fun` keyword balances
    /// perfectly and is not a lambda.
    #[test]
    fn test_sources_parse() {
        for (n, s) in [
            ("proj_arm", SRC_WH_STEP_MONO_PROJ_ARM),
            ("app_some_cf", SRC_WH_STEP_MONO_APP_SOME_CF),
            ("no_name", SRC_NO_NAME_CF_NONE_TRANSFER),
            ("bridge", SRC_STEP_NONE_IMPLIES_IOTA_NONE),
            ("major_agrees", SRC_IOTA_CASE_A_MAJOR_AGREES),
            ("case_a", SRC_IOTA_CASE_A_CONTRADICTION),
            ("case_b", SRC_IOTA_CASE_B_CF_STABLE),
        ] {
            if let Err(e) = crate::test_utils::parse_check(s) {
                panic!("{n} does not parse: {e}");
            }
        }
    }

    /// Every source must be paren-balanced before it reaches the parser.
    #[test]
    fn test_sources_are_balanced() {
        for (n, s) in [
            ("proj_arm", SRC_WH_STEP_MONO_PROJ_ARM),
            ("app_some_cf", SRC_WH_STEP_MONO_APP_SOME_CF),
            ("no_name", SRC_NO_NAME_CF_NONE_TRANSFER),
            ("bridge", SRC_STEP_NONE_IMPLIES_IOTA_NONE),
            ("major_agrees", SRC_IOTA_CASE_A_MAJOR_AGREES),
            ("case_a", SRC_IOTA_CASE_A_CONTRADICTION),
            ("case_b", SRC_IOTA_CASE_B_CF_STABLE),
        ] {
            assert!(Specification::balanced(s), "{n} is not paren-balanced");
        }
    }

    /// The two boundary lemmas must be universe-parametric, and the Type-valued
    /// source must use the Type-valued helper so the substitution to Prop is
    /// total. If a source stopped mentioning either token the Prop variant would
    /// silently be a copy of the Type one.
    #[test]
    fn test_boundary_sources_admit_the_prop_substitution() {
        for (n, s) in [
            ("case_a", SRC_IOTA_CASE_A_CONTRADICTION),
            ("case_b", SRC_IOTA_CASE_B_CF_STABLE),
        ] {
            assert!(s.contains("(C : Type)"), "{n}: no C binder to substitute");
            assert!(
                s.contains("option_none_ne_some_type"),
                "{n}: no Type-valued helper to substitute; the Prop variant would be unsound to \
                 derive by textual replacement"
            );
        }
    }

    /// The simple arms conclude in Eq, so they must NOT reach for Sort 1 helpers.
    #[test]
    fn test_simple_arms_use_prop_helpers() {
        for (n, s) in [
            ("proj_arm", SRC_WH_STEP_MONO_PROJ_ARM),
            ("app_some_cf", SRC_WH_STEP_MONO_APP_SOME_CF),
            ("no_name", SRC_NO_NAME_CF_NONE_TRANSFER),
            ("bridge", SRC_STEP_NONE_IMPLIES_IOTA_NONE),
            ("major_agrees", SRC_IOTA_CASE_A_MAJOR_AGREES),
        ] {
            assert!(
                !s.contains("option_none_ne_some_type") && !s.contains("Eq.substType"),
                "{n} concludes in Eq (Sort 0) but reaches for a Sort 1 helper"
            );
        }
    }
}
