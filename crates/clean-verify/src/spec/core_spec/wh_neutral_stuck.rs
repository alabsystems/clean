// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A δ-dead, recmeta-free const spine has **no step at any budget**.
//!
//! ```text
//! wh_step_none_of_neutral :
//!   recmeta_for (red_rec the_red_env) nm = none
//!     -> is_neutral_red the_red_env e
//!     -> kexpr_const_name (kapp_fn e) = some nm
//!     -> reduce_once_red_wh the_red_env wh e = none
//! ```
//!
//! ## Why this is the brick step monotonicity turns on
//!
//! The faithful loop's step is budget-indexed only through ι, so a step that
//! fires at one budget fires the same way at the next exactly when the pre-pass
//! result that made ι fire is **stable**. That result is constructor-headed —
//! that is why the rule matched — so it carries no recursor metadata (`i2`,
//! `RecEnvCtorNoRecMeta`) and no definitional value (`i8`,
//! `RecEnvCtorNoDefVal`). This lemma turns those two facts into the statement
//! that the step function has nothing to do with it, at any budget, which is
//! the hypothesis restricted monotonicity needs in order to transport it.
//!
//! ## Two things that make the proof short
//!
//! **Quantify over the pre-pass, not over fuel.** The statement is about an
//! arbitrary `wh : KExpr -> OptionType KExpr`. "Stuck at every budget" is then
//! an instance, and the proof never mentions fuel at all.
//!
//! **Induct on `is_neutral_red`, not on `KExpr`.** `is_neutral_red` is already
//! precisely the δ-dead const spine, with a `const` arm carrying its own
//! δ-deadness evidence and an `app` arm closing under application. Its recursor
//! therefore supplies the spine induction *and* the fact that the head is not a
//! lambda in one move. That second part is what dissolves the awkward step: to
//! compute `reduce_app_head_red_wh` one must know the head's constructor, and a
//! `KExpr.rec` on the whole term does not expose it. Here the two surviving
//! shapes — `const` and `app` — both take the `opt_app_ilift` branch, so
//! `reduce_app_head_neutral_is_ilift` is two `Eq.refl`s.
//!
//! `kapp_fn (app f a) = kapp_fn f` is definitional, so the `app` arm's head
//! hypothesis *is* the induction hypothesis's premise — no transport is needed.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// `delta_reduct` of a bare constant, the term both δ lemmas talk about.
const DR: &str = "(delta_reduct (red_def the_red_env) (KExpr.const n us))";
/// Its definitional value lookup.
const DV: &str = "(defval_for (red_def the_red_env) n)";

impl Specification {
    /// The δ half, the head-shape lemma, and the spine induction.
    pub(super) fn add_wh_neutral_stuck(&mut self) -> Result<(), SpecError> {
        self.add_defval_none_inversion()?;
        self.add_neutral_of_dead_head()?;
        self.add_neutral_head_is_ilift()?;
        self.add_neutral_step_none()?;
        Ok(())
    }

    /// The δ half: a constant whose spine does not δ-unfold has no value.
    ///
    /// This is the CONVERSE of `delta_reduct_none_of_defval_none`, which the
    /// tree already has; the direction needed here does not exist, because
    /// nothing until now had to read δ-deadness *out* of a neutral witness.
    fn add_defval_none_inversion(&mut self) -> Result<(), SpecError> {
        let spine = "(apply_spine (kapp_args (KExpr.const n us)) v)";
        let cont = "(fun (o : OptionType KExpr) => opt_bind KExpr KExpr o \
             (fun (val : KExpr) => OptionType.some KExpr \
             (apply_spine (kapp_args (KExpr.const n us)) val)))";
        let src = format!(
            "def defval_none_of_delta_reduct_none (n : Name) (us : ListType Level) \
             (hd : Eq (OptionType KExpr) {DR} (OptionType.none KExpr)) : \
             Eq (OptionType KExpr) {DV} (OptionType.none KExpr) := \
             OptionType.rec KExpr (fun (o : OptionType KExpr) => \
             Eq (OptionType KExpr) {DV} o -> Eq (OptionType KExpr) {DV} (OptionType.none KExpr)) \
             (fun (h : Eq (OptionType KExpr) {DV} (OptionType.none KExpr)) => h) \
             (fun (v : KExpr) (h : Eq (OptionType KExpr) {DV} (OptionType.some KExpr v)) => \
             option_none_ne_some KExpr {spine} \
             (Eq (OptionType KExpr) {DV} (OptionType.none KExpr)) \
             (Eq.trans (OptionType KExpr) (OptionType.none KExpr) {DR} \
             (OptionType.some KExpr {spine}) \
             (Eq.symm (OptionType KExpr) {DR} (OptionType.none KExpr) hd) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) {cont} {DV} \
             (OptionType.some KExpr v) h))) \
             {DV} (Eq.refl (OptionType KExpr) {DV})",
        );
        debug_assert!(Self::balanced(&src), "defval none inversion parens");
        self.add_recursive_def(
            &src,
            "defval_none_of_delta_reduct_none: a constant whose spine does not delta-unfold has no \
             definitional value. The CONVERSE of delta_reduct_none_of_defval_none, which the tree \
             already had; this direction was missing because nothing until now needed to read \
             delta-deadness back OUT of a neutral witness. \
             \
             Convoy on the value lookup. If it is none the hypothesis already is the goal; if it \
             is some v then delta_reduct computes to some (apply_spine (kapp_args e) v), \
             contradicting the assumption that it is none. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Build a neutral witness from a δ-dead head.
    ///
    /// `wh_step_none_of_neutral` consumes `is_neutral_red`, but the place that
    /// needs it — the ι pre-pass result — arrives as a *head-name equation*
    /// plus `i8`'s δ-deadness, not as a witness. This converts one into the
    /// other.
    ///
    /// The goal is `Type`-valued, so the impossible arms take
    /// `option_none_ne_some_type`. That is the OPPOSITE of every goal in
    /// `wh_fuel_adequacy`, which concludes in `Eq` and needs the `Sort 0` form;
    /// the two helpers have identical argument order, so the universe has to be
    /// checked per module rather than carried over by habit.
    fn add_neutral_of_dead_head(&mut self) -> Result<(), SpecError> {
        let head = |x: &str| {
            format!(
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.some Name nm)"
            )
        };
        let mot = |x: &str| format!("({} -> is_neutral_red the_red_env {x})", head(x));
        // Nothing but a const gives a head name, so every other shape is absurd.
        let dead = |term: &str, binders: &str| {
            format!(
                "(fun {binders} (h : {hd}) => option_none_ne_some_type Name nm \
                 (is_neutral_red the_red_env {term}) h)",
                hd = head(term),
            )
        };
        let arms = [
            dead("(KExpr.sort n)", "(n : Level)"),
            dead("(KExpr.bvar i)", "(i : Nat)"),
            // kapp_fn (app f a) = kapp_fn f DEFINITIONALLY, so the hypothesis is
            // already in the induction hypothesis's form — no transport.
            format!(
                "(fun (f : KExpr) (a : KExpr) (ihf : {motf}) (_iha : {mota}) (h : {happ}) => \
                 is_neutral_red.app the_red_env f a (ihf h))",
                motf = mot("f"),
                mota = mot("a"),
                happ = head("(KExpr.app f a)"),
            ),
            dead(
                "(KExpr.lam ty b)",
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {}) (_cb : {})",
                    mot("ty"),
                    mot("b")
                ),
            ),
            dead(
                "(KExpr.pi ty b)",
                &format!(
                    "(ty : KExpr) (b : KExpr) (_cty : {}) (_cb : {})",
                    mot("ty"),
                    mot("b")
                ),
            ),
            // No name injectivity needed: delta_reduct_eq_none_of_defval_none
            // takes the head equation directly.
            format!(
                "(fun (n : Name) (us : ListType Level) (h : {hc}) => \
                 is_neutral_red.const the_red_env n us \
                 (delta_reduct_eq_none_of_defval_none (red_def the_red_env) \
                 (KExpr.const n us) nm h hdef))",
                hc = head("(KExpr.const n us)"),
            ),
            dead(
                "(KExpr.let_ ty v b)",
                &format!(
                    "(ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : {}) (_c2 : {}) (_c3 : {})",
                    mot("ty"),
                    mot("v"),
                    mot("b")
                ),
            ),
            dead(
                "(KExpr.proj s i sub)",
                &format!("(s : Name) (i : Nat) (sub : KExpr) (_cs : {})", mot("sub")),
            ),
            dead("(KExpr.lit v)", "(v : Nat)"),
        ];
        let src = format!(
            "def is_neutral_red_of_dead_head (nm : Name) (hdef : Eq (OptionType KExpr) \
             (defval_for (red_def the_red_env) nm) (OptionType.none KExpr)) (e : KExpr) : \
             {mote} := KExpr.rec (fun (x : KExpr) => {motx}) {arms} e",
            mote = mot("e"),
            motx = mot("x"),
            arms = arms.join(" "),
        );
        debug_assert!(Self::balanced(&src), "neutral of dead head parens");
        self.add_recursive_def(
            &src,
            "is_neutral_red_of_dead_head: a term whose spine head is a constant with no \
             definitional value IS a neutral. Nine-arm recursion on the expression; only const \
             and app can carry a head name, and the other seven arms are discharged by the \
             head-name equation being impossible there. \
             \
             Needed because the consumer of neutrality — the iota pre-pass result — arrives as a \
             head-name equation plus i8's delta-deadness rather than as a witness. The app arm \
             needs no transport, since kapp_fn (app f a) = kapp_fn f definitionally; the const \
             arm needs no name injectivity, since delta_reduct_eq_none_of_defval_none accepts the \
             head equation as given. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// A neutral head is never a lambda, so the step takes the ilift branch.
    fn add_neutral_head_is_ilift(&mut self) -> Result<(), SpecError> {
        let goal = |x: &str| {
            format!(
                "Eq (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh a {x} cf) \
                 (opt_app_ilift_wh the_red_env wh {x} a cf)"
            )
        };
        let src = format!(
            "def reduce_app_head_neutral_is_ilift (wh : KExpr -> OptionType KExpr) (a : KExpr) \
             (cf : OptionType KExpr) (f : KExpr) (hn : is_neutral_red the_red_env f) : {goalf} := \
             is_neutral_red.rec the_red_env \
             (fun (x : KExpr) (_h : is_neutral_red the_red_env x) => {goalx}) \
             (fun (n : Name) (us : ListType Level) \
             (_hd : Eq (OptionType KExpr) {DR} (OptionType.none KExpr)) => \
             Eq.refl (OptionType KExpr) \
             (opt_app_ilift_wh the_red_env wh (KExpr.const n us) a cf)) \
             (fun (g : KExpr) (b : KExpr) (_hg : is_neutral_red the_red_env g) \
             (_ih : {goalg}) => Eq.refl (OptionType KExpr) \
             (opt_app_ilift_wh the_red_env wh (KExpr.app g b) a cf)) f hn",
            goalf = goal("f"),
            goalx = goal("x"),
            goalg = goal("g"),
        );
        debug_assert!(Self::balanced(&src), "neutral ilift parens");
        self.add_recursive_def(
            &src,
            "reduce_app_head_neutral_is_ilift: when the head of an application is NEUTRAL, the \
             step takes the opt_app_ilift branch. \
             \
             reduce_app_head_red cases on the head's constructor, and only the lam arm differs — \
             every other arm is opt_app_ilift. A neutral is a constant or an application, never a \
             lambda, so both reachable arms agree and each is Eq.refl. Inducting on \
             is_neutral_red rather than on KExpr is what makes this available: the neutral \
             witness exposes the head shape, which a recursion on the whole term does not. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The spine induction: no step, at any budget.
    fn add_neutral_step_none(&mut self) -> Result<(), SpecError> {
        let no_step = |x: &str| {
            format!(
                "Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh {x}) \
                 (OptionType.none KExpr)"
            )
        };
        let motive = format!(
            "(fun (x : KExpr) (_h : is_neutral_red the_red_env x) => {head} -> {none})",
            head = Self::head_is("x"),
            none = no_step("x"),
        );
        // The head const carries no metadata, so the iota chain short-circuits at
        // its second level — that is iota_reduct_whc_none_of_no_recmeta, which
        // reads the chain from the same whc_layers the inverter does.
        let app_arm = format!(
            "(fun (f : KExpr) (a : KExpr) (hnf : is_neutral_red the_red_env f) \
             (ih : {headf} -> {nonef}) (hh : {headapp}) => \
             Eq.trans (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a)) \
             (opt_app_ilift_wh the_red_env wh f a (OptionType.none KExpr)) \
             (OptionType.none KExpr) \
             (Eq.trans (OptionType KExpr) (reduce_once_red_wh the_red_env wh (KExpr.app f a)) \
             (reduce_app_head_red_wh the_red_env wh a f (OptionType.none KExpr)) \
             (opt_app_ilift_wh the_red_env wh f a (OptionType.none KExpr)) \
             (Eq.cong (OptionType KExpr) (OptionType KExpr) \
             (fun (o : OptionType KExpr) => reduce_app_head_red_wh the_red_env wh a f o) \
             (reduce_once_red_wh the_red_env wh f) (OptionType.none KExpr) (ih hh)) \
             (reduce_app_head_neutral_is_ilift wh a (OptionType.none KExpr) f hnf)) \
             (iota_reduct_whc_none_of_no_recmeta (red_rec the_red_env) wh (KExpr.app f a) nm \
             hh hrm))",
            headf = Self::head_is("f"),
            nonef = no_step("f"),
            headapp = Self::head_is("(KExpr.app f a)"),
        );
        let src = format!(
            "def wh_step_none_of_neutral (wh : KExpr -> OptionType KExpr) (nm : Name) \
             (hrm : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) nm) \
             (OptionType.none RecMeta)) (e : KExpr) (hn : is_neutral_red the_red_env e) : \
             {heade} -> {nonee} := \
             is_neutral_red.rec the_red_env {motive} \
             (fun (n : Name) (us : ListType Level) \
             (hd : Eq (OptionType KExpr) {DR} (OptionType.none KExpr)) \
             (_hh : {headconst}) => defval_none_of_delta_reduct_none n us hd) \
             {app_arm} e hn",
            heade = Self::head_is("e"),
            nonee = no_step("e"),
            headconst = Self::head_is("(KExpr.const n us)"),
        );
        debug_assert!(Self::balanced(&src), "neutral step none parens");
        self.add_recursive_def(
            &src,
            "wh_step_none_of_neutral: a delta-dead, recmeta-free const spine has NO STEP AT ANY \
             BUDGET. Stated over an arbitrary pre-pass function rather than at a quantified fuel, \
             so `stuck at every budget` is an instance and the proof never mentions fuel. \
             \
             Induction on is_neutral_red. The const arm is the delta half outright: the step on a \
             bare constant IS its value lookup, and the neutral witness says that lookup is empty. \
             The app arm rewrites the head-reduct to none by the induction hypothesis (available \
             because kapp_fn (app f a) = kapp_fn f is definitional, so the head hypothesis is \
             already in the right form), takes the ilift branch since a neutral is not a lambda, \
             and finishes with the iota short-circuit at the missing metadata. \
             \
             This is the fact step monotonicity turns on: the pre-pass result that made iota fire \
             is constructor-headed, hence carries no recmeta (i2) and no defval (i8), hence is \
             genuinely stuck by this lemma, hence stable under more fuel. DerivedProved, zero \
             axiom_deps.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    /// The helper must match the universe of its declaration's GOAL, and this
    /// module deliberately contains both kinds.
    ///
    /// The three step lemmas conclude in `Eq` (`Sort 0`) and must use the plain
    /// helpers. `is_neutral_red_of_dead_head` concludes in `is_neutral_red`,
    /// which is `Type`-valued, so it must use the `_type` form. The two families
    /// take identical arguments and differ only in universe, which is exactly
    /// why this is worth pinning per declaration rather than per file — an
    /// earlier file-level ban here was too coarse and fired on correct code.
    #[test]
    fn test_sort_one_helpers_match_their_goal() {
        let src = include_str!("wh_neutral_stuck.rs");
        let body = src.split("mod tests").next().expect("module body");
        let mut fns: Vec<(&str, &str)> = Vec::new();
        for part in body.split("    fn add_").skip(1) {
            let name = part.split('(').next().unwrap_or("");
            fns.push((name, part));
        }
        // Doc comments sit ABOVE their fn, so splitting on the fn line files each
        // comment with the PRECEDING function. Prose naming a helper would then
        // be read as a use of it.
        let code_only = |part: &str| {
            part.lines()
                .filter(|l| !l.trim_start().starts_with("//"))
                .collect::<Vec<_>>()
                .join("\n")
        };
        assert!(
            fns.len() >= 4,
            "expected the module's four builders, saw {}",
            fns.len()
        );
        for (name, part) in fns {
            let type_valued = name == "neutral_of_dead_head";
            let uses_type_helper = code_only(part).contains("option_none_ne_some_type");
            assert_eq!(
                uses_type_helper,
                type_valued,
                "{name}: goal is {}, so it must {} the _type helper",
                if type_valued {
                    "Type-valued"
                } else {
                    "an Eq (Sort 0)"
                },
                if type_valued { "use" } else { "not use" },
            );
        }
    }

    /// The ι short-circuit must be APPLIED, not re-assumed. An earlier staging
    /// took it as a hypothesis so the spine induction could be validated before
    /// the discharge existed; shipping that form would have left a second
    /// assumed premise in the tree for no reason.
    #[test]
    fn test_iota_shortcircuit_is_applied_not_assumed() {
        // Split off the test module: this file reads ITSELF, so a banned string
        // written in an assertion below would otherwise trip the assertion.
        let src = include_str!("wh_neutral_stuck.rs");
        let src = src.split("mod tests").next().expect("module body");
        assert!(
            src.contains("iota_reduct_whc_none_of_no_recmeta (red_rec the_red_env)"),
            "the iota short-circuit must be applied here"
        );
        assert!(
            !src.contains("(hcnone :"),
            "the iota short-circuit is proved; it must not be carried as a hypothesis"
        );
    }

    /// The statement must quantify over the pre-pass rather than over fuel —
    /// that is what keeps fuel out of the proof entirely.
    #[test]
    fn test_quantifies_over_the_prepass_not_fuel() {
        let src = include_str!("wh_neutral_stuck.rs");
        let body = src.split("mod tests").next().expect("module body");
        assert!(
            body.contains("(wh : KExpr -> OptionType KExpr)"),
            "the lemma must take an arbitrary pre-pass function"
        );
        assert!(
            !body.contains("whnf_fuel_red_wh the_red_env"),
            "no fuel-indexed loop should appear: quantifying over wh makes it unnecessary"
        );
    }
}
