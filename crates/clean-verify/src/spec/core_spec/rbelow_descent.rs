// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Descent: the components of a weak head normal form are accessible whenever
//! the original term is.
//!
//! This is the third structural prerequisite of the completeness capstone,
//! after fuel adequacy (`fuel_adequacy.rs`) and fuel monotonicity
//! (`defeq_fuel_mono.rs`). The capstone recurses by reducing both sides to whnf
//! and then descending into the components; for that recursion to be
//! well-founded, each component must carry its own accessibility witness. That
//! is what this module produces:
//!
//! ```text
//! whnf_component_acc :
//!   whnf_fuel_red the_red_env n a = some r -> subexpr_step c r
//!     -> rbelow_plus_acc a -> rbelow_plus_acc c
//! ```
//!
//! ## Why a reflexive closure is needed
//!
//! `rbelow_plus` is *strict*, but `a` need not step at all — a term already in
//! whnf has `r = a`. So the reduction leg contributes a **reflexive-transitive**
//! relation, and only the final `subexpr_step` makes the descent strict. Hence
//! `rbelow_rtc`, and the composition lemma
//! `rbelow x y -> rbelow_rtc y z -> rbelow_plus x z`: one strict step on the
//! left of any number of steps is strictly below.
//!
//! ## Direction bookkeeping
//!
//! Three relations here run in opposite directions and mixing them up would
//! produce a plausible-looking term that proves nothing:
//!
//! | relation | reading |
//! |---|---|
//! | `whnf_red_step_star renv a r` | `a` reduces **to** `r` (downward) |
//! | `rbelow x y` | `x` is **below** `y` (so reduction gives `rbelow r a`) |
//! | `subexpr_step c p` | `c` is an immediate child **of** `p` |
//!
//! `rbelow`'s `red` arm already encodes the flip (`whnf_red_step … y x ->
//! rbelow x y`), so the star bridge here has motive `fun x y _ => rbelow_rtc y
//! x` — reversed, deliberately.
//!
//! `whnf_red_step_star` is cons-style (a step at the *front*), while the
//! accumulation needed here appends at the *back*, so `rbelow_rtc_snoc` does
//! the turning. That mirrors `red_step_star_to_whnf_red_step_star`, which
//! solves the same cons/snoc mismatch one layer down.
//!
//! `DerivedProved` throughout, empty axiom closures; `rbelow_rtc` is
//! census-neutral.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The reflexive-transitive `rbelow` closure and the descent lemmas.
    pub(super) fn add_rbelow_descent(&mut self) -> Result<(), SpecError> {
        self.add_rbelow_rtc()?;
        self.add_rbelow_descent_lemmas()?;
        Ok(())
    }

    /// `rbelow_rtc x z`: `x` is at or below `z`.
    fn add_rbelow_rtc(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            "inductive rbelow_rtc : KExpr -> KExpr -> Type\n\
             | refl : forall (x : KExpr), rbelow_rtc x x\n\
             | step : forall (x : KExpr) (y : KExpr) (z : KExpr), rbelow x y -> \
             rbelow_rtc y z -> rbelow_rtc x z",
            "rbelow_rtc x z: x is AT OR BELOW z in the algorithm's order — the \
             reflexive-transitive closure of rbelow, as against rbelow_plus which is the strict \
             transitive closure. The reflexive case is not a technicality: a term already in weak \
             head normal form does not step at all, so its reduction leg is genuinely empty and a \
             strict relation could not describe it. Census-neutral.",
        )?;
        Ok(())
    }

    fn add_rbelow_descent_lemmas(&mut self) -> Result<(), SpecError> {
        // Append at the far end. rbelow_rtc is cons-style (a step at the front)
        // but the star bridge below accumulates at the back.
        self.add_recursive_def(
            "def rbelow_rtc_snoc (x : KExpr) (y : KExpr) (hxy : rbelow_rtc x y) : \
             forall (z : KExpr), rbelow y z -> rbelow_rtc x z := \
             rbelow_rtc.rec \
             (fun (p : KExpr) (q : KExpr) (_h : rbelow_rtc p q) => \
             forall (z : KExpr), rbelow q z -> rbelow_rtc p z) \
             (fun (p : KExpr) (z : KExpr) (hz : rbelow p z) => \
             rbelow_rtc.step p z z hz (rbelow_rtc.refl z)) \
             (fun (p : KExpr) (q : KExpr) (r : KExpr) (hpq : rbelow p q) \
             (_hqr : rbelow_rtc q r) \
             (ih : forall (z : KExpr), rbelow r z -> rbelow_rtc q z) \
             (z : KExpr) (hz : rbelow r z) => \
             rbelow_rtc.step p q z hpq (ih z hz)) \
             x y hxy",
            "rbelow_rtc_snoc: append one rbelow step at the FAR end of an rbelow_rtc chain. The \
             closure is cons-style (its step constructor prepends), but the reduction-star bridge \
             accumulates at the back, so something has to turn the list around; this is it. The \
             same cons/snoc mismatch red_step_star_to_whnf_red_step_star solves one layer down. \
             DerivedProved, zero axiom_deps.",
        )?;

        // One strict step below anything at-or-below z is strictly below z.
        self.add_recursive_def(
            "def rbelow_plus_of_step_rtc (x : KExpr) (y : KExpr) (z : KExpr) (hxy : rbelow x y) \
             (hyz : rbelow_rtc y z) : rbelow_plus x z := \
             rbelow_rtc.rec \
             (fun (p : KExpr) (q : KExpr) (_h : rbelow_rtc p q) => \
             forall (w : KExpr), rbelow w p -> rbelow_plus w q) \
             (fun (p : KExpr) (w : KExpr) (hw : rbelow w p) => rbelow_plus.base w p hw) \
             (fun (p : KExpr) (q : KExpr) (r : KExpr) (hpq : rbelow p q) \
             (_hqr : rbelow_rtc q r) \
             (ih : forall (w : KExpr), rbelow w q -> rbelow_plus w r) \
             (w : KExpr) (hw : rbelow w p) => \
             rbelow_plus.step w p r hw (ih p hpq)) \
             y z hyz x hxy",
            "rbelow_plus_of_step_rtc: one STRICT step below something at-or-below z is strictly \
             below z. This is what makes the capstone's descent strict even when the reduction \
             leg is empty — the subexpr_step at the end supplies the strictness that the \
             reduction may not. DerivedProved, zero axiom_deps.",
        )?;

        // The reduction leg. Note the reversed motive: reduction goes downward,
        // so `a` reducing to `r` means `r` is BELOW `a`.
        self.add_recursive_def(
            "def whnf_red_step_star_to_rbelow_rtc (a : KExpr) (r : KExpr) \
             (h : whnf_red_step_star the_red_env a r) : rbelow_rtc r a := \
             whnf_red_step_star.rec the_red_env \
             (fun (p : KExpr) (q : KExpr) (_h : whnf_red_step_star the_red_env p q) => \
             rbelow_rtc q p) \
             (fun (p : KExpr) => rbelow_rtc.refl p) \
             (fun (p : KExpr) (q : KExpr) (s : KExpr) \
             (hstep : whnf_red_step the_red_env p q) \
             (_hstar : whnf_red_step_star the_red_env q s) \
             (ih : rbelow_rtc s q) => \
             rbelow_rtc_snoc s q ih p (rbelow.red q p hstep)) \
             a r h",
            "whnf_red_step_star_to_rbelow_rtc: a multi-step weak-head reduction places its result \
             at or below its source in the algorithm's order. The motive is REVERSED on purpose \
             (fun p q _ => rbelow_rtc q p): reduction runs downward, so `a` reducing to `r` means \
             `r` is below `a`, and rbelow's red arm already encodes that flip. Each cons-style \
             step is appended at the back with rbelow_rtc_snoc. DerivedProved, zero axiom_deps.",
        )?;

        // The executable loop's leg, via the existing soundness chain.
        self.add_recursive_def(
            "def whnf_fuel_red_rbelow_rtc (n : Nat) (a : KExpr) (r : KExpr) \
             (h : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) \
             (OptionType.some KExpr r)) : rbelow_rtc r a := \
             whnf_red_step_star_to_rbelow_rtc a r \
             (red_step_star_to_whnf_red_step_star the_red_env a r \
             (whnf_fuel_red_reaches_sound the_red_env n a r h))",
            "whnf_fuel_red_rbelow_rtc: whatever the EXECUTABLE whnf loop returns is at or below \
             its input in the algorithm's order. Composes the loop's reach-soundness \
             (whnf_fuel_red_reaches_sound) with the snoc/cons bridge and the order embedding. \
             This is the form the capstone consumes, since the capstone runs the loop rather than \
             the relation. DerivedProved, zero axiom_deps.",
        )?;

        // Accessibility is inherited downward — the field of the intro node.
        self.add_recursive_def(
            "def rbelow_plus_acc_inv (e : KExpr) (h : rbelow_plus_acc e) : \
             forall (e2 : KExpr), rbelow_plus e2 e -> rbelow_plus_acc e2 := \
             rbelow_plus_acc.rec \
             (fun (x : KExpr) (_h : rbelow_plus_acc x) => \
             forall (e2 : KExpr), rbelow_plus e2 x -> rbelow_plus_acc e2) \
             (fun (x : KExpr) \
             (hfield : forall (e2 : KExpr), rbelow_plus e2 x -> rbelow_plus_acc e2) \
             (_ih : forall (e2 : KExpr), rbelow_plus e2 x -> \
             forall (e3 : KExpr), rbelow_plus e3 e2 -> rbelow_plus_acc e3) => hfield) \
             e h",
            "rbelow_plus_acc_inv: accessibility is inherited by everything strictly below — \
             literally the field of the intro node, projected out. DerivedProved, zero \
             axiom_deps.",
        )?;

        // THE DESCENT LEMMA the capstone's recursion consumes.
        self.add_recursive_def(
            "def whnf_component_acc (n : Nat) (a : KExpr) (r : KExpr) (c : KExpr) \
             (hr : Eq (OptionType KExpr) (whnf_fuel_red the_red_env n a) \
             (OptionType.some KExpr r)) \
             (hc : subexpr_step c r) (hacc : rbelow_plus_acc a) : rbelow_plus_acc c := \
             rbelow_plus_acc_inv a hacc c \
             (rbelow_plus_of_step_rtc c r a (rbelow.sub c r hc) \
             (whnf_fuel_red_rbelow_rtc n a r hr))",
            "whnf_component_acc: DESCENT — if the executable loop takes a to r and c is an \
             immediate subexpression of r, then c inherits a's accessibility. This is what makes \
             the completeness capstone's recursion well-founded: it reduces both sides to weak \
             head normal form and then recurses into the components, and each component needs its \
             own well-foundedness witness to hand to the recursive call. The strictness comes \
             from the subexpr_step, not from the reduction — a term already in whnf does not step \
             at all. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}
