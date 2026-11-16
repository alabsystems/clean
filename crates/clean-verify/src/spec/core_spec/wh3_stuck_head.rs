// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What STUCKNESS actually tells you about a term's spine head.
//!
//! Every existing supplier for `hnf3`'s application residual —
//! `hnf3_app_residual_of_{rigid,dead_const_head,under_applied,bvar_major}` —
//! binds its `wh3_stuck_at` hypothesis and never uses it. The four covered
//! classes are covered *unconditionally*, with the class facts handed in by the
//! caller. **These are the first lemmas in the tree that derive a structural
//! fact from `wh3_stuck_at` itself.**
//!
//! # Two holes in the ARGUMENT, not just the proof
//!
//! The case analysis on a stuck application's head has always skipped `lam` and
//! live-δ `const` on the grounds that the step would have fired — with nothing
//! in the tree saying so. Both are now stated and proved.
//!
//! The δ one closes by a different mechanism than the obvious guess. For an
//! APPLIED const, δ does **not** fire through `iota_reduct_whc3`; that chain
//! never consults `defval_for` at all. It fires through the **congruence**
//! path — `reduce_once_red_wh3`'s const arm makes `cf` a `wstep`,
//! `reduce_app_head_red_wh3` ilifts it, and `opt_app_ilift3`'s `wstep` arm
//! rebuilds the application. So δ does fire under application, at every spine
//! depth.
//!
//! # A row the audit had missed entirely
//!
//! `let_`. `reduce_once_red_wh3`'s `let_` arm is unconditionally `wstep`, so a
//! stuck term is never a `let_` — and unlike `lam`, this closes even at a bare
//! term.
//!
//! # A bound worth stating
//!
//! A **bare** lam IS wh3-stuck, so `wh3_stuck_app_head_not_lam` closes only at
//! the immediate function part. A lam at a DEEP spine head needs a further
//! descent, which is not written here.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// What stuckness forces about the spine head.
    pub(super) fn add_wh3_stuck_head(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_OPT_APP_ILIFT3_STUCK_INV,
            "opt_app_ilift3_stuck_inv: an ilift that reports stuck forces the HEAD's own step to have been stuck. A WhStepR convoy. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_APP_HEAD_STUCK_FORCES_HEAD_STUCK,
            "wh3_app_head_stuck_forces_head_stuck: nine-arm KExpr.rec on the head. Eight arms delegate to the ilift convoy; the LAM arm dies outright, because reduce_app_head_red_wh3's lam arm is unconditionally wstep. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_APP_HEAD_NOT_LAM,
            "wh3_stuck_app_head_not_lam: a stuck application's function part is never a lambda. \\
\\
This was a hole in the ARGUMENT, not merely in the proof: the case analysis on a stuck application's head has always skipped lam on the grounds that the step would have beta-fired, and nothing in the tree said so. \\
\\
CAVEAT, stated because it bounds the lemma: a BARE lam IS wh3-stuck (reduce_once_red_wh3's lam arm is wstuck), so this closes only at the immediate function part. A lam sitting at a DEEP spine head needs a further descent, which is not written. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_APP_FN_STUCK,
            "wh3_stuck_app_fn_stuck: a stuck application has a stuck function part. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_KAPP_FN_STUCK,
            "wh3_stuck_kapp_fn_stuck: a stuck term's SPINE HEAD is stuck. The spine induction. \\
\\
Composed with wh3_stuck_const_delta_dead it derives guarded operational delta-deadness. It does NOT derive the stronger raw-name absence currently required by hnf3_app_residual_of_dead_const_head; wrong universe arity is another cause of stuckness. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            &wh3_stuck_const_name_no_delta_src(),
            "wh3_stuck_const_name_no_delta: a stuck constant has no guarded instantiated value at its actual universe arguments. Nine-arm KExpr.rec; the const arm transports the name while retaining those arguments. Wrong arity can explain stuckness even when a raw definition exists. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_APP_HEAD_NO_DELTA,
            "wh3_stuck_app_head_no_delta: a stuck application's spine head is delta-DEAD. \\
\\
The second hole in the argument, and it closes by a DIFFERENT mechanism than expected. For an APPLIED const, delta does not fire through iota_reduct_whc3 at all — that chain never consults definition-value lookup. It fires through the CONGRUENCE path: reduce_once_red_wh3's const arm makes cf a wstep, reduce_app_head_red_wh3 ilifts it, and opt_app_ilift3's wstep arm rebuilds the application. So delta does fire under application, at every spine depth, and stuckness excludes a successful guarded lookup at the actual head universe arguments. \\
\\
Stated in the kexpr_const_name form the other suppliers use, which is strictly more usable than the literal KExpr.const form. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_NOT_LET,
            "wh3_stuck_not_let: a stuck term is never a let_. THE ROW THE AUDIT ORIGINALLY MISSED. Unlike lam, this one closes even at a bare term: reduce_once_red_wh3's let_ arm is unconditionally wstep. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH3_STUCK_KAPP_FN_NOT_LET,
            "wh3_stuck_kapp_fn_not_let: a stuck term's spine head is never a let_. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_OPT_APP_ILIFT3_STUCK_INV: &str = "def opt_app_ilift3_stuck_inv (renv : RedEnv) (wh : KExpr -> OptionType KExpr) (f : KExpr) (a : KExpr) (cf : WhStepR) : @Eq WhStepR (opt_app_ilift3 renv wh f a cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck := @WhStepR.rec (fun (o : WhStepR) => @Eq WhStepR (opt_app_ilift3 renv wh f a o) WhStepR.wstuck -> @Eq WhStepR o WhStepR.wstuck) (fun (_h : @Eq WhStepR (opt_app_ilift3 renv wh f a WhStepR.wstuck) WhStepR.wstuck) => @Eq.refl WhStepR WhStepR.wstuck) (fun (h : @Eq WhStepR (opt_app_ilift3 renv wh f a WhStepR.wstarved) WhStepR.wstuck) => wh_stuck_ne_starved (@Eq WhStepR WhStepR.wstarved WhStepR.wstuck) (Eq.symm WhStepR WhStepR.wstarved WhStepR.wstuck h)) (fun (e2 : KExpr) (h : @Eq WhStepR (opt_app_ilift3 renv wh f a (WhStepR.wstep e2)) WhStepR.wstuck) => wh_stuck_ne_step (KExpr.app e2 a) (@Eq WhStepR (WhStepR.wstep e2) WhStepR.wstuck) (Eq.symm WhStepR (WhStepR.wstep (KExpr.app e2 a)) WhStepR.wstuck h)) cf";

const SRC_WH3_APP_HEAD_STUCK_FORCES_HEAD_STUCK: &str = "def wh3_app_head_stuck_forces_head_stuck (k : Nat) (a : KExpr) (cf : WhStepR) (f : KExpr) : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a f cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck := @KExpr.rec (fun (y : KExpr) => @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a y cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (fun (sl : Level) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.sort sl) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.sort sl) a cf h) (fun (bi : Nat) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.bvar bi) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.bvar bi) a cf h) (fun (af : KExpr) (aa : KExpr) (_ihaf : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a af cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (_ihaa : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a aa cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.app af aa) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.app af aa) a cf h) (fun (lty : KExpr) (lb : KExpr) (_ihlty : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a lty cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (_ihlb : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a lb cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.lam lty lb) cf) WhStepR.wstuck) => wh_stuck_ne_step (instantiate lb a) (@Eq WhStepR cf WhStepR.wstuck) (Eq.symm WhStepR (WhStepR.wstep (instantiate lb a)) WhStepR.wstuck h)) (fun (pty : KExpr) (pb : KExpr) (_ihpty : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a pty cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (_ihpb : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a pb cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.pi pty pb) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.pi pty pb) a cf h) (fun (cn : Name) (cus : ListType Level) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.const cn cus) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.const cn cus) a cf h) (fun (zty : KExpr) (zv : KExpr) (zb : KExpr) (_ihzty : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a zty cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (_ihzv : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a zv cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (_ihzb : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a zb cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.let_ zty zv zb) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.let_ zty zv zb) a cf h) (fun (psn : Name) (pix : Nat) (psub : KExpr) (_ihpsub : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a psub cf) WhStepR.wstuck -> @Eq WhStepR cf WhStepR.wstuck) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.proj psn pix psub) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.proj psn pix psub) a cf h) (fun (lv : Nat) (h : @Eq WhStepR (reduce_app_head_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) a (KExpr.lit lv) cf) WhStepR.wstuck) => opt_app_ilift3_stuck_inv the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) (KExpr.lit lv) a cf h) f";

const SRC_WH3_STUCK_APP_HEAD_NOT_LAM: &str = "def wh3_stuck_app_head_not_lam (k : Nat) (lty : KExpr) (lb : KExpr) (a : KExpr) (hs : wh3_stuck_at k (KExpr.app (KExpr.lam lty lb) a)) : Empty := wh_stuck_ne_step_type (instantiate lb a) Empty (Eq.symm WhStepR (WhStepR.wstep (instantiate lb a)) WhStepR.wstuck hs)";

const SRC_WH3_STUCK_APP_FN_STUCK: &str = "def wh3_stuck_app_fn_stuck (k : Nat) (f : KExpr) (a : KExpr) (hs : wh3_stuck_at k (KExpr.app f a)) : wh3_stuck_at k f := wh3_app_head_stuck_forces_head_stuck k a (reduce_once_red_wh3 the_red_env (fun (e2 : KExpr) => whnf_fuel_red_wh3 the_red_env k e2) f) f hs";

const SRC_WH3_STUCK_KAPP_FN_STUCK: &str = "def wh3_stuck_kapp_fn_stuck (k : Nat) (e : KExpr) : wh3_stuck_at k e -> wh3_stuck_at k (kapp_fn e) := @KExpr.rec (fun (x : KExpr) => wh3_stuck_at k x -> wh3_stuck_at k (kapp_fn x)) (fun (sl : Level) (h : wh3_stuck_at k (KExpr.sort sl)) => h) (fun (bi : Nat) (h : wh3_stuck_at k (KExpr.bvar bi)) => h) (fun (af : KExpr) (aa : KExpr) (ihaf : wh3_stuck_at k af -> wh3_stuck_at k (kapp_fn af)) (_ihaa : wh3_stuck_at k aa -> wh3_stuck_at k (kapp_fn aa)) (h : wh3_stuck_at k (KExpr.app af aa)) => ihaf (wh3_stuck_app_fn_stuck k af aa h)) (fun (lty : KExpr) (lb : KExpr) (_ihlty : wh3_stuck_at k lty -> wh3_stuck_at k (kapp_fn lty)) (_ihlb : wh3_stuck_at k lb -> wh3_stuck_at k (kapp_fn lb)) (h : wh3_stuck_at k (KExpr.lam lty lb)) => h) (fun (pty : KExpr) (pb : KExpr) (_ihpty : wh3_stuck_at k pty -> wh3_stuck_at k (kapp_fn pty)) (_ihpb : wh3_stuck_at k pb -> wh3_stuck_at k (kapp_fn pb)) (h : wh3_stuck_at k (KExpr.pi pty pb)) => h) (fun (cn : Name) (cus : ListType Level) (h : wh3_stuck_at k (KExpr.const cn cus)) => h) (fun (zty : KExpr) (zv : KExpr) (zb : KExpr) (_ihzty : wh3_stuck_at k zty -> wh3_stuck_at k (kapp_fn zty)) (_ihzv : wh3_stuck_at k zv -> wh3_stuck_at k (kapp_fn zv)) (_ihzb : wh3_stuck_at k zb -> wh3_stuck_at k (kapp_fn zb)) (h : wh3_stuck_at k (KExpr.let_ zty zv zb)) => h) (fun (psn : Name) (pix : Nat) (psub : KExpr) (_ihpsub : wh3_stuck_at k psub -> wh3_stuck_at k (kapp_fn psub)) (h : wh3_stuck_at k (KExpr.proj psn pix psub)) => h) (fun (lv : Nat) (h : wh3_stuck_at k (KExpr.lit lv)) => h) e";

fn wh3_stuck_const_name_no_delta_src() -> String {
    let query = |subject: &str| {
        format!("(kdef_value_at (red_def the_red_env) nm (kexpr_const_levels {subject}))")
    };
    let goal = |subject: &str| {
        format!(
            "@Eq (OptionType KExpr) {} (@OptionType.some KExpr dv) -> \
             @Eq (OptionType Name) (kexpr_const_name {subject}) (@OptionType.some Name nm) -> \
             wh3_stuck_at k {subject} -> Empty",
            query(subject)
        )
    };
    let const_arm = "wh_stuck_ne_step_type dv Empty \
         (Eq.symm WhStepR (WhStepR.wstep dv) WhStepR.wstuck \
           (Eq.subst (OptionType KExpr) \
             (fun (o : OptionType KExpr) => @Eq WhStepR \
               (opt_step_bind KExpr o WhStepR.wstuck (fun (zv : KExpr) => WhStepR.wstep zv)) \
               WhStepR.wstuck) \
             (kdef_value_at (red_def the_red_env) nm cus) (@OptionType.some KExpr dv) hdef \
             (Eq.subst Name \
               (fun (zn : Name) => @Eq WhStepR \
                 (opt_step_bind KExpr (kdef_value_at (red_def the_red_env) zn cus) \
                   WhStepR.wstuck (fun (zv : KExpr) => WhStepR.wstep zv)) WhStepR.wstuck) \
               cn nm (option_some_inj Name cn nm hn) hst)))";
    let arms: [(&str, &[&str], &str); 9] = [
        ("(sl : Level)", &[], "(KExpr.sort sl)"),
        ("(bi : Nat)", &[], "(KExpr.bvar bi)"),
        (
            "(af : KExpr) (aa : KExpr)",
            &["af", "aa"],
            "(KExpr.app af aa)",
        ),
        (
            "(lty : KExpr) (lb : KExpr)",
            &["lty", "lb"],
            "(KExpr.lam lty lb)",
        ),
        (
            "(pty : KExpr) (pb : KExpr)",
            &["pty", "pb"],
            "(KExpr.pi pty pb)",
        ),
        (
            "(cn : Name) (cus : ListType Level)",
            &[],
            "(KExpr.const cn cus)",
        ),
        (
            "(zty : KExpr) (zv : KExpr) (zb : KExpr)",
            &["zty", "zv", "zb"],
            "(KExpr.let_ zty zv zb)",
        ),
        (
            "(psn : Name) (pix : Nat) (psub : KExpr)",
            &["psub"],
            "(KExpr.proj psn pix psub)",
        ),
        ("(lv : Nat)", &[], "(KExpr.lit lv)"),
    ];
    let mut minors = String::new();
    for (index, (payload, children, form)) in arms.iter().enumerate() {
        let ihs = children
            .iter()
            .enumerate()
            .map(|(i, child)| format!("(_ih{i} : {})", goal(child)))
            .collect::<Vec<_>>()
            .join(" ");
        let arm = if index == 5 {
            const_arm
        } else {
            "option_none_ne_some_type Name nm Empty hn"
        };
        minors.push_str(&format!(
            "(fun {payload} {ihs} \
              (hdef : @Eq (OptionType KExpr) {} (@OptionType.some KExpr dv)) \
              (hn : @Eq (OptionType Name) (kexpr_const_name {form}) (@OptionType.some Name nm)) \
              (hst : wh3_stuck_at k {form}) => {arm}) ",
            query(form)
        ));
    }
    format!(
        "def wh3_stuck_const_name_no_delta (k : Nat) (nm : Name) (dv : KExpr) (x : KExpr) : {} := \
         @KExpr.rec (fun (z : KExpr) => {}) {minors} x",
        goal("x"),
        goal("z")
    )
}

const SRC_WH3_STUCK_APP_HEAD_NO_DELTA: &str = "def wh3_stuck_app_head_no_delta (k : Nat) (f : KExpr) (a : KExpr) (nm : Name) (dv : KExpr) (hdef : @Eq (OptionType KExpr) (kdef_value_at (red_def the_red_env) nm (kexpr_const_levels (kapp_fn (KExpr.app f a)))) (@OptionType.some KExpr dv)) (hh : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (@OptionType.some Name nm)) (hs : wh3_stuck_at k (KExpr.app f a)) : Empty := wh3_stuck_const_name_no_delta k nm dv (kapp_fn (KExpr.app f a)) hdef hh (wh3_stuck_kapp_fn_stuck k (KExpr.app f a) hs)";

const SRC_WH3_STUCK_NOT_LET: &str = "def wh3_stuck_not_let (k : Nat) (zty : KExpr) (zv : KExpr) (zb : KExpr) (hs : wh3_stuck_at k (KExpr.let_ zty zv zb)) : Empty := wh_stuck_ne_step_type (instantiate zb zv) Empty (Eq.symm WhStepR (WhStepR.wstep (instantiate zb zv)) WhStepR.wstuck hs)";

const SRC_WH3_STUCK_KAPP_FN_NOT_LET: &str = "def wh3_stuck_kapp_fn_not_let (k : Nat) (e : KExpr) (zty : KExpr) (zv : KExpr) (zb : KExpr) (hf : @Eq KExpr (kapp_fn e) (KExpr.let_ zty zv zb)) (hs : wh3_stuck_at k e) : Empty := wh3_stuck_not_let k zty zv zb (Eq.subst KExpr (fun (x : KExpr) => wh3_stuck_at k x) (kapp_fn e) (KExpr.let_ zty zv zb) hf (wh3_stuck_kapp_fn_stuck k e hs))";

#[cfg(test)]
mod tests {
    use super::{wh3_stuck_const_name_no_delta_src, SRC_WH3_STUCK_APP_HEAD_NO_DELTA};
    use crate::test_utils::parse_check;

    #[test]
    fn guarded_stuck_head_sources_parse_and_retain_actual_levels() {
        for source in [
            wh3_stuck_const_name_no_delta_src(),
            SRC_WH3_STUCK_APP_HEAD_NO_DELTA.to_string(),
        ] {
            parse_check(&source).expect("guarded stuck-head definition parses");
            assert!(source.contains("kdef_value_at"));
            assert!(source.contains("kexpr_const_levels"));
            assert!(!source.contains("defval_for"));
        }
    }
}
