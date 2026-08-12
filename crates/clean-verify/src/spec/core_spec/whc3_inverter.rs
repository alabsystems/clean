// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CPS inversion of the THREE-WAY iota chain.
//!
//! ```text
//! iota_reduct_whc3_some_inv : iota_reduct_whc3 env wh e = WhStepR.wstep e'
//!   -> (recname meta major wmajor cname rule, <six lookup equations> -> <reduct> -> C)
//!   -> C
//! ```
//!
//! # Why this is the brick everything else waits on
//!
//! A three-way step does **not** embed into `whnf_red_step`: that relation's
//! only non-β congruences are `app_left` and `proj`, so nothing lets a δ or a
//! nested ι fire *inside an argument* — and a recursor's major premise is an
//! argument, which is exactly where the pre-pass works. Weakening the target to
//! the transitive closure does not help, and `rbelow` is equally blind (its two
//! arms are `whnf_red_step` and `subexpr_step`, and `subexpr_step` only goes
//! down). `wh_soundness.rs` records the same finding for the two-way faithful
//! loop, in its own words: *"not merely unproved, it is unstatable."*
//!
//! So the soundness route runs through `par_reduces_cd_star`, which **does**
//! have argument congruence — and that route starts by inverting the chain.
//!
//! # The one thing that could not be copied from the two-way inverter
//!
//! `opt_bind`'s failure branch is `none`, fixed. `opt_step_bind`'s is a
//! **parameter**, so from `opt_step_bind A o d f = wstep r` alone *nothing*
//! follows: `d` could itself be `wstep r`. The `none` arm needs the caller to
//! rule that out.
//!
//! That obligation is taken as a hypothesis rather than by fixing `d`, so **one**
//! lemma serves both defaults the chain uses — `wh_stuck_ne_step` at five levels
//! and `wh_starved_ne_step` at the pre-pass — instead of two near-copies free to
//! drift apart.
//!
//! The six *lookup* equations are unchanged from the two-way inverter, and that
//! is not a coincidence: `wh` still returns `OptionType KExpr`, so only the
//! chain's own result type moved.
//!
//! `DerivedProved`, empty axiom closures.

use super::iota_prepass::MAJOR_IDX;
use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Both inverters, at both universes, plus `wstep` injectivity.
    pub(super) fn add_whc3_inverter(&mut self) -> Result<(), SpecError> {
        self.add_opt_step_bind_inverter_at("_type", "Type")?;
        self.add_opt_step_bind_inverter_at("", "Prop")?;
        self.add_wh_step_inj()?;
        self.add_whc3_inverter_at("_type", "Type")?;
        self.add_whc3_inverter_at("", "Prop")?;
        Ok(())
    }

    /// The per-level CPS inverter for `opt_step_bind`, in BOTH universes.
    fn add_opt_step_bind_inverter_at(&mut self, suffix: &str, univ: &str) -> Result<(), SpecError> {
        let kont = "(forall (w : A), Eq (OptionType A) o (OptionType.some A w) -> \
                    Eq WhStepR (f w) (WhStepR.wstep r) -> C)";
        let kont0 = "(forall (w : A), Eq (OptionType A) o0 (OptionType.some A w) -> \
                     Eq WhStepR (f w) (WhStepR.wstep r) -> C)";
        let src = format!(
            "def opt_step_bind_some_inv{suffix} (A : Type) (o : OptionType A) \
             (d : WhStepR) (f : A -> WhStepR) (r : KExpr) (C : {univ}) \
             (hd : Eq WhStepR d (WhStepR.wstep r) -> C) \
             (h : Eq WhStepR (opt_step_bind A o d f) (WhStepR.wstep r)) \
             (k : {kont}) : C := \
             OptionType.rec A \
             (fun (o0 : OptionType A) => \
             Eq WhStepR (opt_step_bind A o0 d f) (WhStepR.wstep r) -> {kont0} -> C) \
             (fun (h0 : Eq WhStepR (opt_step_bind A (OptionType.none A) d f) \
             (WhStepR.wstep r)) \
             (_k0 : forall (w : A), Eq (OptionType A) (OptionType.none A) \
             (OptionType.some A w) -> \
             Eq WhStepR (f w) (WhStepR.wstep r) -> C) => hd h0) \
             (fun (w : A) \
             (h0 : Eq WhStepR (opt_step_bind A (OptionType.some A w) d f) \
             (WhStepR.wstep r)) \
             (k0 : forall (w0 : A), Eq (OptionType A) (OptionType.some A w) \
             (OptionType.some A w0) -> \
             Eq WhStepR (f w0) (WhStepR.wstep r) -> C) => \
             k0 w (Eq.refl (OptionType A) (OptionType.some A w)) h0) \
             o h k"
        );
        debug_assert!(Self::balanced(&src), "opt_step_bind inverter parens");
        self.add_recursive_def(
            &src,
            &format!(
                "opt_step_bind_some_inv{suffix}: CPS inversion of ONE opt_step_bind level, \
                 concluding at C : {univ}. From opt_step_bind A o d f = wstep r, recover the \
                 witness w with o = some w and f w = wstep r, delivered to a continuation — the \
                 fragment has no Sigma or Exists. \
                 \
                 It carries one hypothesis opt_bind_some_inv does not, and the reason is \
                 structural: opt_step_bind's failure branch is CHOSEN rather than fixed at none, \
                 so from the equation alone nothing follows — d could itself be wstep r. hd is \
                 the caller's proof that it is not. Taking it as a hypothesis rather than fixing \
                 d at wstuck is what lets ONE lemma serve both defaults the iota chain uses: \
                 five levels supply wh_stuck_ne_step, the pre-pass supplies wh_starved_ne_step. \
                 \
                 By OptionType.rec on o: the none arm reduces opt_step_bind to d and hands h0 to \
                 hd; the some arm reduces it to f w, which IS the continuation's second premise. \
                 Emitted at both universes because the kernel is non-cumulative and callers \
                 conclude at both. DerivedProved, zero axiom_deps."
            ),
        )?;
        Ok(())
    }

    /// `WhStepR.wstep` injectivity — the analogue of `option_some_inj`.
    ///
    /// The two-way inverter hands back `some reduct = some e'` and its callers
    /// strip it with `option_some_inj`. The three-way one hands back an equation
    /// between `wstep` constructors, and nothing in the tree could strip that
    /// before this: `wh3_stability.rs` proves step stability by nested `KExpr.rec`
    /// convoys, so it dodged the need rather than supplying it.
    fn add_wh_step_inj(&mut self) -> Result<(), SpecError> {
        let src = "def wh_step_inj (x : KExpr) (y : KExpr) \
             (h : Eq WhStepR (WhStepR.wstep x) (WhStepR.wstep y)) : Eq KExpr x y := \
             Eq.cong WhStepR KExpr \
             (fun (o : WhStepR) => WhStepR.rec (fun (_o : WhStepR) => KExpr) x x \
             (fun (z : KExpr) => z) o) \
             (WhStepR.wstep x) (WhStepR.wstep y) h";
        debug_assert!(Self::balanced(src), "wh_step_inj parens");
        self.add_recursive_def(
            src,
            "wh_step_inj: WhStepR.wstep injectivity. The exact analogue of option_some_inj — a \
             WhStepR.rec payload projector transported by Eq.cong, iota-reducing on a literal \
             wstep at both ends, with the two nullary arms filled by x so the projector is total. \
             \
             Needed because the three-way inverter's reduct equation is between wstep \
             constructors rather than between some constructors. Prop only: Eq is Prop-valued, so \
             there is no second universe to serve. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The six-level chain inverter, at one universe.
    fn add_whc3_inverter_at(&mut self, suffix: &str, univ: &str) -> Result<(), SpecError> {
        let src = Self::whc3_inverter_src(suffix, univ);
        let inv = format!("opt_step_bind_some_inv{suffix}");
        let starved = format!("wh_starved_ne_step{suffix}");
        debug_assert!(Self::balanced(&src), "whc3 inverter parens");
        debug_assert_eq!(
            src.matches(&format!("{inv} ")).count(),
            6,
            "six chain levels, six inversions"
        );
        debug_assert_eq!(
            src.matches(&format!("({starved} e2 C)")).count(),
            1,
            "exactly ONE level defaults to starvation, and it must be the pre-pass"
        );
        self.add_recursive_def(&src, &Self::whc3_inverter_desc(suffix, univ))?;
        Ok(())
    }

    /// The inverter's source, built from the SAME layer strings the chain is.
    pub(super) fn whc3_inverter_src(suffix: &str, univ: &str) -> String {
        let mi = MAJOR_IDX;
        let reduct = Self::whc_reduct();
        // The SAME layer strings the chain itself is built from — shared, not
        // re-transcribed, so the inversion cannot drift out from under its
        // subject.
        let [l2, l3, l4, l5, l6, l7] = Self::whc3_layers();
        let inv = format!("opt_step_bind_some_inv{suffix}");
        let stuck = format!("wh_stuck_ne_step{suffix}");
        let starved = format!("wh_starved_ne_step{suffix}");
        let kont = format!(
            "(forall (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) \
             (cname : Name) (rule : RecRule), \
             Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name recname) -> \
             Eq (OptionType RecMeta) (recmeta_for env recname) (OptionType.some RecMeta meta) -> \
             Eq (OptionType KExpr) (list_head (list_drop {mi} (kapp_args e))) \
             (OptionType.some KExpr major) -> \
             Eq (OptionType KExpr) (wh major) (OptionType.some KExpr wmajor) -> \
             Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) \
             (OptionType.some Name cname) -> \
             Eq (OptionType RecRule) (recrule_for env recname cname) \
             (OptionType.some RecRule rule) -> \
             Eq WhStepR (WhStepR.wstep {reduct}) (WhStepR.wstep e2) -> \
             C)"
        );
        let src = format!(
            "def iota_reduct_whc3_some_inv{suffix} (env : RecEnv) \
             (wh : KExpr -> OptionType KExpr) \
             (e : KExpr) (e2 : KExpr) (C : {univ}) \
             (h : Eq WhStepR (iota_reduct_whc3 env wh e) (WhStepR.wstep e2)) \
             (k : {kont}) : C := \
             {inv} Name (kexpr_const_name (kapp_fn e)) WhStepR.wstuck {l2} e2 C \
             ({stuck} e2 C) h \
             (fun (recname : Name) \
             (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) \
             (OptionType.some Name recname)) \
             (h1r : Eq WhStepR ({l2} recname) (WhStepR.wstep e2)) => \
             {inv} RecMeta (recmeta_for env recname) WhStepR.wstuck {l3} e2 C \
             ({stuck} e2 C) h1r \
             (fun (meta : RecMeta) \
             (h2 : Eq (OptionType RecMeta) (recmeta_for env recname) \
             (OptionType.some RecMeta meta)) \
             (h2r : Eq WhStepR ({l3} meta) (WhStepR.wstep e2)) => \
             {inv} KExpr (list_head (list_drop {mi} (kapp_args e))) WhStepR.wstuck \
             {l4} e2 C ({stuck} e2 C) h2r \
             (fun (major : KExpr) \
             (h3 : Eq (OptionType KExpr) (list_head (list_drop {mi} (kapp_args e))) \
             (OptionType.some KExpr major)) \
             (h3r : Eq WhStepR ({l4} major) (WhStepR.wstep e2)) => \
             {inv} KExpr (wh major) WhStepR.wstarved {l5} e2 C \
             ({starved} e2 C) h3r \
             (fun (wmajor : KExpr) \
             (hw : Eq (OptionType KExpr) (wh major) (OptionType.some KExpr wmajor)) \
             (h4r : Eq WhStepR ({l5} wmajor) (WhStepR.wstep e2)) => \
             {inv} Name (kexpr_const_name (kapp_fn wmajor)) WhStepR.wstuck {l6} e2 C \
             ({stuck} e2 C) h4r \
             (fun (cname : Name) \
             (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) \
             (OptionType.some Name cname)) \
             (h5r : Eq WhStepR ({l6} cname) (WhStepR.wstep e2)) => \
             {inv} RecRule (recrule_for env recname cname) WhStepR.wstuck {l7} e2 C \
             ({stuck} e2 C) h5r \
             (fun (rule : RecRule) \
             (h5 : Eq (OptionType RecRule) (recrule_for env recname cname) \
             (OptionType.some RecRule rule)) \
             (h6r : Eq WhStepR ({l7} rule) (WhStepR.wstep e2)) => \
             k recname meta major wmajor cname rule h1 h2 h3 hw h4 h5 h6r))))))"
        );
        src
    }

    fn whc3_inverter_desc(suffix: &str, univ: &str) -> String {
        format!(
            "iota_reduct_whc3_some_inv{suffix}: CPS inversion of iota_reduct_whc3's six-level \
                 opt_step_bind chain, recovering the recursor name, its metadata, the raw major, \
                 ITS WHNF, the constructor name and the rule, together with every lookup equation \
                 and the reduct identity. The three-way twin of iota_reduct_whc_some_inv, \
                 concluding at C : {univ}. \
                 \
                 The six LOOKUP equations are unchanged from the two-way inverter, and that is \
                 not a coincidence: wh still returns OptionType KExpr, so only the CHAIN's result \
                 type moved. What changes is the hypothesis — WhStepR.wstep e2 rather than \
                 OptionType.some KExpr e2 — and the reduct equation, now between wstep \
                 constructors, which wh_step_inj exists to strip. \
                 \
                 Six nested opt_step_bind_some_inv, each supplied with the refutation of its OWN \
                 default: wh_stuck_ne_step at five levels and wh_starved_ne_step at level four, \
                 the pre-pass. That single substitution is where the whole three-way distinction \
                 shows up in the inversion, and it is why an opt_bind-shaped inverter could not \
                 have been reused. \
                 \
                 WHY IT IS NEEDED: a three-way step does not embed into whnf_red_step — that \
                 relation has no congruence letting a delta or a nested iota fire inside an \
                 argument, and a recursor's major premise is an argument. So loop soundness must \
                 target par_reduces_cd_star, which does have argument congruence, exactly as \
                 wh_soundness.rs did for the two-way faithful loop; and that route starts here. \
                 DerivedProved, zero axiom_deps."
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The inverter is only correct if it inverts the chain the spec actually
    /// registers. Sharing `whc3_layers` is what guarantees that, so pin the
    /// sharing: every layer string must appear in the inverter, twice — once as
    /// the `f` argument to its own level, once inside the following level's
    /// hypothesis type.
    #[test]
    fn test_inverter_inverts_the_registered_chain() {
        let src = Specification::whc3_inverter_src("", "Prop");
        for (n, layer) in Specification::whc3_layers().iter().enumerate() {
            // The layers NEST — l2 contains l3 contains l4 … — so occurrences
            // compound. Each layer is spliced twice at its own level (once as
            // the `f` argument, once in the following level's hypothesis type),
            // and every occurrence of the layer above carries one more. Hence
            // 2*(n+1), not 2. Getting this wrong is what the test caught on its
            // first run, which is the point of pinning an exact count rather
            // than a containment.
            assert_eq!(
                src.matches(layer.as_str()).count(),
                2 * (n + 1),
                "layer {n} appears the wrong number of times — it has drifted \
                 from the chain, and a six-level CPS inversion cannot survive that"
            );
        }
        assert!(Specification::balanced(&src), "inverter parens");
        // The continuation must conclude at the DECLARED parameter e2. An
        // earlier draft wrote `e'` here, left over from a rename; the parser
        // reads that as `e` — a different bound variable — and the kernel
        // reported it only as `fvar mismatch: FVarId(3) vs FVarId(12)`, which
        // names neither. A prime is not a syntax error in this fragment, it is
        // a silent rebinding.
        assert!(
            !src.contains("e'"),
            "a primed identifier survives; the parser will resolve it to `e`"
        );
        assert_eq!(
            src.matches("(WhStepR.wstep e2)").count(),
            8,
            "the target term appears once per level plus the two statement sites"
        );
    }

    /// The pre-pass is the ONE level that may report starvation. If a later edit
    /// makes a second level starve, or makes the pre-pass fail as merely stuck,
    /// the false-stuck bug is back and this catches it in the Rust rather than
    /// 26 minutes into a spec build.
    /// Emit every generated source under a marker, so a scratchpad batch can be
    /// assembled from the REAL strings rather than hand-copied. These register
    /// EARLY in the sequence (inside `add_iota_prepass`), so an elaboration
    /// failure here aborts the build and leaves everything after it unchecked —
    /// which is exactly the case the scratchpad exists to diagnose, since it
    /// appends to an already-built spec and reports each candidate on its own.
    #[test]
    fn test_emit_sources_for_scratchpad() {
        for (suffix, univ) in [("_type", "Type"), ("", "Prop")] {
            eprintln!("WHC3SRC {}", Specification::whc3_inverter_src(suffix, univ));
        }
    }

    #[test]
    fn test_exactly_one_layer_starves() {
        let [l2, ..] = Specification::whc3_layers();
        assert_eq!(
            l2.matches("WhStepR.wstarved").count(),
            1,
            "exactly one level may report starvation, and it must be the pre-pass"
        );
        assert_eq!(
            l2.matches("WhStepR.wstuck").count(),
            4,
            "l2 nests four stuck-defaulting levels below it"
        );
    }
}
