// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stuck spines are ι- and δ-immune.
//!
//! The scoping audit of this program listed as an open gap: *"that genuine
//! kernel whnf results are iota-immune is not established."* It is the premise
//! `par_reduces_cd_star_neutral_app_inv_eq` needs
//! (`wall_a_completeness.rs:1912-1918` asks for `iota_neutral f` **and**
//! `iota_immune (KExpr.app f a)`), and it is the reason the landed one-round
//! `def_eq_whnf_complete` carries `iota_whnf` hypotheses that nothing
//! discharges.
//!
//! For the shape the completeness capstone actually meets — the `stuck` arm of
//! `whnf_noredex_class`, an application on a stuck head — the gap closes, and
//! for a structural reason worth stating:
//!
//! **`whnf_stuck_head` has no `const` arm.** Its six constructors
//! (`whnf_progress.rs:153-159`) are `sort`, `pi`, `app` on a stuck head,
//! `proj`, `projw`, and `lit`. No constant, no bound variable, no lambda. So
//! the head of a stuck application spine is always a sort, pi, literal or
//! projection — never something `kexpr_const_name` can name.
//!
//! Both reducts short-circuit on exactly that lookup: `iota_reduct` and
//! `delta_reduct` each begin `opt_bind (kexpr_const_name (kapp_fn e)) …`
//! (`delta_step.rs:61`). A `none` head therefore makes both `none`, with no
//! environment condition at all.
//!
//! The bridge is definitional: `kapp_fn (app f a)` unfolds to `kapp_fn f`
//! (`expr_model.rs:377-380`), so a fact about the stuck head *is* a fact about
//! the whole application.
//!
//! ## Scope
//!
//! This settles immunity for **stuck** spines only. A `const`-headed neutral —
//! the `is_neutral` case of `is_whnf` — is a different matter: whether it
//! δ-unfolds depends on whether the environment defines that constant, which is
//! exactly what `consts_defined_red` records. That case genuinely needs the
//! premise, and no structural argument removes it.
//!
//! `DerivedProved` throughout, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Stuck heads carry no constant name, hence no ι or δ step.
    pub(super) fn add_stuck_immunity(&mut self) -> Result<(), SpecError> {
        self.add_stuck_head_no_const()?;
        self.add_delta_reduct_head_none()?;
        self.add_stuck_app_immunity()?;
        Ok(())
    }

    /// The structural fact: a stuck spine's head is never a constant.
    fn add_stuck_head_no_const(&mut self) -> Result<(), SpecError> {
        // Six arms. `app` and `proj` have recursive premises and so carry
        // induction hypotheses; `projw`'s premise is an `is_whnf`, a different
        // inductive, so it carries none — the distinction that shifts every
        // later binder if got wrong.
        let none_at = |x: &str| {
            format!("Eq (OptionType Name) (kexpr_const_name (kapp_fn {x})) (OptionType.none Name)")
        };
        let refl = "Eq.refl (OptionType Name) (OptionType.none Name)";

        self.add_recursive_def(
            &format!(
                "def whnf_stuck_head_no_const (f : KExpr) (hs : whnf_stuck_head f) : {goal} := \
                 whnf_stuck_head.rec \
                 (fun (x : KExpr) (_h : whnf_stuck_head x) => {motive}) \
                 (fun (n : Level) => {refl}) \
                 (fun (pty : KExpr) (pbody : KExpr) => {refl}) \
                 (fun (af : KExpr) (aa : KExpr) (_hf : whnf_stuck_head af) \
                 (ih : {ih_af}) => ih) \
                 (fun (s : Name) (i : Nat) (sub : KExpr) (_hsub : whnf_stuck_head sub) \
                 (_ih : {ih_sub}) => {refl}) \
                 (fun (s : Name) (i : Nat) (sub : KExpr) (_hw : is_whnf sub) => {refl}) \
                 (fun (v : Nat) => {refl}) \
                 f hs",
                goal = none_at("f"),
                motive = none_at("x"),
                ih_af = none_at("af"),
                ih_sub = none_at("sub"),
            ),
            "whnf_stuck_head_no_const: the head of a stuck spine NEVER carries a constant name. \
             Structural, and the reason is that whnf_stuck_head simply has no const arm — its six \
             constructors are sort, pi, app-on-a-stuck-head, proj, projw and lit. The app arm is \
             the only one that recurses, and it recurses to exactly the statement, because \
             kapp_fn (app f a) unfolds to kapp_fn f; every other arm computes to none directly. \
             This is what closes the iota-immunity gap the program's scoping audit recorded as \
             open. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The δ mirror of the in-tree `iota_reduct_head_none`.
    fn add_delta_reduct_head_none(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def delta_reduct_head_none (env : DefEnv) (x : KExpr) \
             (hn : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.none Name)) : \
             Eq (OptionType KExpr) (delta_reduct env x) (OptionType.none KExpr) := \
             Eq.cong (OptionType Name) (OptionType KExpr) \
             (fun (o : OptionType Name) => opt_bind Name KExpr o \
             (fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) \
             (fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args x) val)))) \
             (kexpr_const_name (kapp_fn x)) (OptionType.none Name) hn",
            "delta_reduct_head_none: if a term's spine head carries no constant name then \
             delta_reduct is none — its outermost opt_bind short-circuits. The delta mirror of \
             the in-tree iota_reduct_head_none (faithful_red_env.rs:1014), proved the same way, \
             by Eq.cong on the head-lookup argument. Only the iota half existed. DerivedProved, \
             zero axiom_deps.",
        )?;
        Ok(())
    }

    /// Therefore an application on a stuck head admits neither step.
    fn add_stuck_app_immunity(&mut self) -> Result<(), SpecError> {
        for (name, envsel, envty, reduct, lemma, greek) in [
            (
                "whnf_stuck_app_iota_immune",
                "red_rec renv",
                "RecEnv",
                "iota_reduct",
                "iota_reduct_head_none",
                "iota",
            ),
            (
                "whnf_stuck_app_delta_immune",
                "red_def renv",
                "DefEnv",
                "delta_reduct",
                "delta_reduct_head_none",
                "delta",
            ),
        ] {
            let _ = envty;
            self.add_recursive_def(
                &format!(
                    "def {name} (renv : RedEnv) (f : KExpr) (a : KExpr) \
                     (hs : whnf_stuck_head f) : \
                     Eq (OptionType KExpr) ({reduct} ({envsel}) (KExpr.app f a)) \
                     (OptionType.none KExpr) := \
                     {lemma} ({envsel}) (KExpr.app f a) (whnf_stuck_head_no_const f hs)"
                ),
                &format!(
                    "{name}: an application on a stuck head admits NO {greek} step, over ANY \
                     reduction environment and with no side conditions. Immediate from \
                     whnf_stuck_head_no_const once one notices that kapp_fn (app f a) is \
                     definitionally kapp_fn f, so a fact about the stuck head is a fact about the \
                     whole spine. Together with its twin this supplies the iota_immune premise \
                     that par_reduces_cd_star_neutral_app_inv_eq demands and that the scoping \
                     audit recorded as unestablished — for stuck spines. A const-headed neutral \
                     is a different case and genuinely needs consts_defined_red. DerivedProved, \
                     zero axiom_deps."
                ),
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    /// `whnf_stuck_head` must still have exactly the six constructors this
    /// module's argument depends on. If a `const` or `bvar` arm were ever added
    /// the immunity claim would become FALSE, not merely unproved — a
    /// const-headed spine can δ-unfold.
    #[test]
    fn test_stuck_head_constructor_set_is_unchanged() {
        let whnf_progress = include_str!("whnf_progress.rs");
        let start = whnf_progress
            .find("inductive whnf_stuck_head")
            .expect("whnf_stuck_head is declared");
        let decl = &whnf_progress[start..start + 700];
        let end = decl.find("\",").unwrap_or(decl.len());
        let decl = &decl[..end];
        for arm in [
            "| sort ", "| pi ", "| app ", "| proj ", "| projw ", "| lit ",
        ] {
            assert!(decl.contains(arm), "whnf_stuck_head lost its {arm} arm");
        }
        for forbidden in ["| const ", "| bvar ", "| lam "] {
            assert!(
                !decl.contains(forbidden),
                "whnf_stuck_head gained a {forbidden} arm — stuck-spine immunity is now FALSE, \
                 not merely unproved: such a head can delta-unfold or beta-fire"
            );
        }
        assert_eq!(
            decl.matches("\n| ").count(),
            6,
            "expected exactly six whnf_stuck_head constructors"
        );
    }
}
