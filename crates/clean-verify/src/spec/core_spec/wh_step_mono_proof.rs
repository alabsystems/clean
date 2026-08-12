// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! STEP MONOTONICITY, proved.
//!
//! ```text
//! wh_step_mono_all : (transport from wh1 to wh2 on genuinely stuck results)
//!                  -> reduce_once_red_wh renv wh1 e = some x0
//!                  -> reduce_once_red_wh renv wh2 e = some x0
//! ```
//!
//! This is the premise the whole fuel-adequacy layer was parameterised by. It is
//! stated for two ARBITRARY pre-passes related by a transport, not at a
//! quantified fuel — which is what lets it be instantiated at consecutive
//! budgets later without the statement itself mentioning fuel.
//!
//! ## Why it was hard
//!
//! `opt_app_ilift` branches on the head-reduct: `none` tries ι, `some` takes the
//! congruence. If that reduct could flip `none → some` when the budget grows,
//! the step would return a *different* result and monotonicity would be false.
//! It does flip in general — that is starvation, and it is why plain fuel
//! monotonicity IS false here.
//!
//! It cannot flip where it matters, for an arithmetic reason: `f` and `app f a`
//! share a spine head, hence share `recmeta`, hence share `MAJOR_IDX`. Either
//! the major premise sits inside `f`'s own arguments — and then ι firing on
//! `app f a` means it fired on `f` too, so the reduct was never `none` — or the
//! major IS the outermost argument, and then `f` is one argument short at
//! *every* budget.
//!
//! ## The shape
//!
//! Nine arms. Five give `none` on both sides; `const` and `let_` are
//! budget-independent so the premise is already the goal; `proj` is a convoy
//! plus a congruence. Only `app` does work, and it splits by a convoy on the
//! head NAME — not a recursion on `f`, which would discard the induction
//! hypothesis the `some` case needs.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The two missing order facts, the ι case, the app arm, and the theorem.
    pub(super) fn add_wh_step_mono_proof(&mut self) -> Result<(), SpecError> {
        self.add_order_gaps()?;
        self.add_app_iota_case()?;
        self.add_the_theorem()?;
        Ok(())
    }

    /// `Le n n` and `Le n (succ n)` — neither was in the tree.
    ///
    /// Both fall straight out of `le_zero_n` and `le_succ_succ`; they were
    /// simply never needed until the fuel-indexed induction had to weaken a
    /// bound by one.
    fn add_order_gaps(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_LE_REFL,
            "le_refl: reflexivity of Le, by Nat.rec — zero from le_zero_n, successor from \
             le_succ_succ. Absent from the tree until now because nothing had needed to instantiate \
             a bound at its own index. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_LE_N_SUCC,
            "le_n_succ: every n is at most its successor. One application of le_succ_weaken to \
             le_refl at (succ n). Needed to weaken a bounded induction hypothesis by one step. \
             DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The one case where the pre-pass genuinely matters.
    fn add_app_iota_case(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_WH_STEP_MONO_APP_ITOA_CASE,
            "wh_step_mono_app_iota_case: a const-headed application whose head-reduct is none — the \
             single place in the whole step where the pre-pass can change the answer. \
             \
             Invert the fired iota with iota_reduct_whc_some_inv to recover the recursor name, its \
             metadata, the major, its whnf, the constructor name and the rule. The whnf'd major is \
             constructor-headed and matched a rule, so i2 gives it no recursor metadata and i8 no \
             definitional value; is_neutral_red_of_dead_head and wh_step_none_of_neutral turn that \
             into genuine stuckness, which is exactly what the transport consumes. Move the \
             pre-pass result to the second budget, then re-assemble the same six facts with \
             iota_reduct_whc_some_of_facts. \
             \
             If the head-reduct at the second budget is instead some, the boundary argument \
             applies: nat_lt_le_dichotomy splits on MAJOR_IDX against the spine length, Case A \
             contradicts through iota_case_a_contradiction and Case B through \
             under_applied_step_congr. The dichotomy is TOTAL, so no decidability assumption is \
             needed anywhere — which matters, because assuming one here is precisely the vacuity \
             trap this program has already fallen into once. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }

    /// The app arm, and step monotonicity itself.
    fn add_the_theorem(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_WH_STEP_MONO_APP_ARM,
            "wh_step_mono_app_arm: the application arm, by a two-level convoy. The OUTER convoy is \
             on the head NAME, not a recursion on f — recursing would discard f's induction \
             hypothesis, which the some-head-reduct case needs. No head name routes to \
             no_name_cf_none_transfer; a head name routes to the iota case. The inner convoy is on \
             the head-reduct at the first budget. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_WH_STEP_MONO_ALL,
            "wh_step_mono_all: STEP MONOTONICITY. A step that fires under one pre-pass fires the \
             same way under any pre-pass reachable from it by the transport. \
             \
             Nine arms: sort, bvar, lam, pi and lit give none on both sides so the premise is \
             absurd; const and let_ are budget-independent so the premise IS the goal; proj and app \
             delegate to their arms. \
             \
             Stated over two arbitrary pre-passes rather than at consecutive fuels, so the \
             statement never mentions fuel. That generality is what lets it be instantiated later \
             at whk j and whk (succ j) with the transport supplied by restricted monotonicity — \
             and it works in that direction only because wh_step_none_of_neutral was itself stated \
             over an arbitrary pre-pass. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_LE_REFL: &str = "def le_refl (n : Nat) : Le n n := Nat.rec (fun (m : Nat) => Le m m) (le_zero_n Nat.zero) (fun (k : Nat) (ih : Le k k) => le_succ_succ k k ih) n";

const SRC_LE_N_SUCC: &str = "def le_n_succ (n : Nat) : Le n (Nat.succ n) := le_succ_weaken n (Nat.succ n) (le_refl (Nat.succ n))";

const SRC_WH_STEP_MONO_APP_ITOA_CASE: &str = "def wh_step_mono_app_iota_case (wh1 : KExpr -> OptionType KExpr) (wh2 : KExpr -> OptionType KExpr) (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) (i8 : RecEnvCtorNoDefVal the_red_env) (hT : forall (t : KExpr) (r : KExpr), Eq (OptionType KExpr) (wh1 t) (OptionType.some KExpr r) -> (forall (w : KExpr -> OptionType KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env w r) (OptionType.none KExpr)) -> Eq (OptionType KExpr) (wh2 t) (OptionType.some KExpr r)) (nm : Name) (f : KExpr) (a : KExpr) (x0 : KExpr) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) (hcf : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr)) (hp : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0)) : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0) := iota_reduct_whc_some_inv (red_rec the_red_env) wh1 (KExpr.app f a) x0 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app f a)) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0) (Eq.symm (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app f a)) (Eq.trans (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (opt_app_ilift_wh the_red_env wh1 f a (reduce_once_red_wh the_red_env wh1 f)) (iota_reduct_whc (red_rec the_red_env) wh1 (KExpr.app f a)) (reduce_app_head_const_is_ilift wh1 a (reduce_once_red_wh the_red_env wh1 f) nm f hh) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (o : OptionType KExpr) => opt_app_ilift_wh the_red_env wh1 f a o) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr) hcf))) hp) (fun (recname : Name) (meta : RecMeta) (major : KExpr) (wmajor : KExpr) (cname : Name) (rule : RecRule) (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name recname)) (h2 : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) recname) (OptionType.some RecMeta meta)) (h3 : Eq (OptionType KExpr) (list_head (list_drop (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (kapp_args (KExpr.app f a)))) (OptionType.some KExpr major)) (hw : Eq (OptionType KExpr) (wh1 major) (OptionType.some KExpr wmajor)) (h4 : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cname)) (h5 : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) recname cname) (OptionType.some RecRule rule)) (h6r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args wmajor)) (recrule_num_fields rule)) (kapp_args wmajor)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))) (OptionType.some KExpr x0)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f) o -> (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0))) (fun (hq2 : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.none KExpr)) => Eq.trans (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (iota_reduct_whc (red_rec the_red_env) wh2 (KExpr.app f a)) (OptionType.some KExpr x0) (Eq.trans (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (opt_app_ilift_wh the_red_env wh2 f a (reduce_once_red_wh the_red_env wh2 f)) (iota_reduct_whc (red_rec the_red_env) wh2 (KExpr.app f a)) (reduce_app_head_const_is_ilift wh2 a (reduce_once_red_wh the_red_env wh2 f) nm f hh) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (o : OptionType KExpr) => opt_app_ilift_wh the_red_env wh2 f a o) (reduce_once_red_wh the_red_env wh2 f) (OptionType.none KExpr) hq2)) (Eq.trans (OptionType KExpr) (iota_reduct_whc (red_rec the_red_env) wh2 (KExpr.app f a)) (OptionType.some KExpr (apply_spine (list_drop (Nat.succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) (kapp_args (KExpr.app f a))) (apply_spine (list_drop (Nat.sub (list_length (kapp_args wmajor)) (recrule_num_fields rule)) (kapp_args wmajor)) (apply_spine (list_take (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (kapp_args (KExpr.app f a))) (recrule_rhs rule))))) (OptionType.some KExpr x0) (iota_reduct_whc_some_of_facts (red_rec the_red_env) wh2 (KExpr.app f a) recname meta major wmajor cname rule h1 h2 h3 (hT major wmajor hw (fun (w : KExpr -> OptionType KExpr) => wh_step_none_of_neutral w cname (recenv_ctor_no_recmeta_cname (red_rec the_red_env) recname cname rule wmajor i2 h4 h5) wmajor (is_neutral_red_of_dead_head cname (recenv_ctor_no_defval_cname the_red_env recname cname rule wmajor i8 h4 h5) wmajor h4) h4)) h4 h5) h6r)) (fun (f2 : KExpr) (hq2 : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr f2)) => NatLtLeDichotomy.rec (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args f)) (fun (_d : NatLtLeDichotomy (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args f))) => (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0))) (fun (hlt : Lt (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args f))) => iota_case_a_contradiction wh1 f a recname meta major wmajor cname rule (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0)) h1 h2 h3 hw h4 h5 (lt_to_le_succ (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args f)) hlt) hcf) (fun (hle : Le (list_length (kapp_args f)) (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta))) => option_none_ne_some KExpr f2 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0)) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr f2) (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (reduce_once_red_wh the_red_env wh1 f) (reduce_once_red_wh the_red_env wh2 f) (Eq.symm (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr) hcf) (under_applied_step_congr wh1 wh2 nm meta (Eq.subst Name (fun (z : Name) => Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) z) (OptionType.some RecMeta meta)) recname nm (option_some_inj Name recname nm (Eq.trans (OptionType Name) (OptionType.some Name recname) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name recname) h1) hh)) h2) f hh hle)) hq2)) (nat_lt_le_dichotomy (Nat.add (Nat.add (Nat.add (recmeta_num_params meta) (recmeta_num_motives meta)) (recmeta_num_minors meta)) (recmeta_num_indices meta)) (list_length (kapp_args f)))) (reduce_once_red_wh the_red_env wh2 f) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f)))";

const SRC_WH_STEP_MONO_APP_ARM: &str = "def wh_step_mono_app_arm (wh1 : KExpr -> OptionType KExpr) (wh2 : KExpr -> OptionType KExpr) (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) (i8 : RecEnvCtorNoDefVal the_red_env) (hT : forall (t : KExpr) (r : KExpr), Eq (OptionType KExpr) (wh1 t) (OptionType.some KExpr r) -> (forall (w : KExpr -> OptionType KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env w r) (OptionType.none KExpr)) -> Eq (OptionType KExpr) (wh2 t) (OptionType.some KExpr r)) (f : KExpr) (a : KExpr) (x0 : KExpr) (ihf : forall (y : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.some KExpr y) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr y)) (hp : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0)) : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0) := OptionType.rec Name (fun (on : OptionType Name) => Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) on -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0)) (fun (hn : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.none Name)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) o -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0)) (fun (hcf : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr)) => no_name_cf_none_transfer wh1 wh2 a x0 (reduce_once_red_wh the_red_env wh2 f) f hn (Eq.trans (OptionType KExpr) (reduce_app_head_red_wh the_red_env wh1 a f (OptionType.none KExpr)) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0) (Eq.cong (OptionType KExpr) (OptionType KExpr) (fun (z : OptionType KExpr) => reduce_app_head_red_wh the_red_env wh1 a f z) (OptionType.none KExpr) (reduce_once_red_wh the_red_env wh1 f) (Eq.symm (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr) hcf)) hp)) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.some KExpr f2)) => wh_step_mono_app_some_cf wh1 wh2 a f f2 x0 hq ihf hp) (reduce_once_red_wh the_red_env wh1 f) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f))) (fun (nm : Name) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm)) => OptionType.rec KExpr (fun (o : OptionType KExpr) => Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) o -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.app f a)) (OptionType.some KExpr x0)) (fun (hcf : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.none KExpr)) => wh_step_mono_app_iota_case wh1 wh2 i2 i8 hT nm f a x0 hh hcf hp) (fun (f2 : KExpr) (hq : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.some KExpr f2)) => wh_step_mono_app_some_cf wh1 wh2 a f f2 x0 hq ihf hp) (reduce_once_red_wh the_red_env wh1 f) (Eq.refl (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f))) (kexpr_const_name (kapp_fn f)) (Eq.refl (OptionType Name) (kexpr_const_name (kapp_fn f)))";

const SRC_WH_STEP_MONO_ALL: &str = "def wh_step_mono_all (wh1 : KExpr -> OptionType KExpr) (wh2 : KExpr -> OptionType KExpr) (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) (i8 : RecEnvCtorNoDefVal the_red_env) (hT : forall (t : KExpr) (r : KExpr), Eq (OptionType KExpr) (wh1 t) (OptionType.some KExpr r) -> (forall (w : KExpr -> OptionType KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env w r) (OptionType.none KExpr)) -> Eq (OptionType KExpr) (wh2 t) (OptionType.some KExpr r)) (e : KExpr) : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 e) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 e) (OptionType.some KExpr x0) := KExpr.rec (fun (x : KExpr) => forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 x) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 x) (OptionType.some KExpr x0)) (fun (n : Level) (x0 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.sort n)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.sort n)) (OptionType.some KExpr x0)) h) (fun (i : Nat) (x0 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.bvar i)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.bvar i)) (OptionType.some KExpr x0)) h) (fun (f : KExpr) (a : KExpr) (ihf : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 f) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 f) (OptionType.some KExpr x0)) (_iha : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 a) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 a) (OptionType.some KExpr x0)) (x0 : KExpr) (hp : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.app f a)) (OptionType.some KExpr x0)) => wh_step_mono_app_arm wh1 wh2 i2 i8 hT f a x0 ihf hp) (fun (ty : KExpr) (b : KExpr) (_c1 : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 ty) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 ty) (OptionType.some KExpr x0)) (_c2 : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 b) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 b) (OptionType.some KExpr x0)) (x0 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.lam ty b)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.lam ty b)) (OptionType.some KExpr x0)) h) (fun (ty : KExpr) (b : KExpr) (_c1 : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 ty) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 ty) (OptionType.some KExpr x0)) (_c2 : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 b) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 b) (OptionType.some KExpr x0)) (x0 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.pi ty b)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.pi ty b)) (OptionType.some KExpr x0)) h) (fun (cn : Name) (us : ListType Level) (x0 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.const cn us)) (OptionType.some KExpr x0)) => h) (fun (ty : KExpr) (v : KExpr) (b : KExpr) (_c1 : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 ty) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 ty) (OptionType.some KExpr x0)) (_c2 : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 v) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 v) (OptionType.some KExpr x0)) (_c3 : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 b) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 b) (OptionType.some KExpr x0)) (x0 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.let_ ty v b)) (OptionType.some KExpr x0)) => h) (fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : forall (x0 : KExpr), Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 sub) (OptionType.some KExpr x0) -> Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 sub) (OptionType.some KExpr x0)) (x0 : KExpr) (hp : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.proj s i sub)) (OptionType.some KExpr x0)) => wh_step_mono_proj_arm wh1 wh2 s i sub x0 ihsub hp) (fun (v : Nat) (x0 : KExpr) (h : Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh1 (KExpr.lit v)) (OptionType.some KExpr x0)) => option_none_ne_some KExpr x0 (Eq (OptionType KExpr) (reduce_once_red_wh the_red_env wh2 (KExpr.lit v)) (OptionType.some KExpr x0)) h) e";

#[cfg(test)]
mod tests {
    use super::*;

    /// The cheap gate: parse each source without elaborating it.
    #[test]
    fn test_sources_parse() {
        for (n, s) in [
            ("le_refl", SRC_LE_REFL),
            ("le_n_succ", SRC_LE_N_SUCC),
            ("iota_case", SRC_WH_STEP_MONO_APP_ITOA_CASE),
            ("app_arm", SRC_WH_STEP_MONO_APP_ARM),
            ("all", SRC_WH_STEP_MONO_ALL),
        ] {
            if let Err(e) = crate::test_utils::parse_check(s) {
                panic!("{n} does not parse: {e}");
            }
        }
    }

    #[test]
    fn test_sources_are_balanced() {
        for (n, s) in [
            ("le_refl", SRC_LE_REFL),
            ("le_n_succ", SRC_LE_N_SUCC),
            ("iota_case", SRC_WH_STEP_MONO_APP_ITOA_CASE),
            ("app_arm", SRC_WH_STEP_MONO_APP_ARM),
            ("all", SRC_WH_STEP_MONO_ALL),
        ] {
            assert!(Specification::balanced(s), "{n} is not paren-balanced");
        }
    }

    /// The app arm must convoy on the head NAME, not recurse on f. Recursing
    /// would discard f's induction hypothesis, which the some-head-reduct case
    /// needs, and the arm would be unprovable.
    #[test]
    fn test_app_arm_convoys_rather_than_recurses() {
        assert!(
            SRC_WH_STEP_MONO_APP_ARM.contains("kexpr_const_name (kapp_fn f)"),
            "the app arm must split on the head name"
        );
        assert!(
            !SRC_WH_STEP_MONO_APP_ARM.contains("KExpr.rec"),
            "the app arm must NOT recurse on f: that discards the induction hypothesis"
        );
    }

    /// The theorem must be stated over arbitrary pre-passes. If it were phrased
    /// at consecutive fuels, the instantiation against restricted monotonicity
    /// would not typecheck.
    #[test]
    fn test_theorem_is_prepass_generic_not_fuel_indexed() {
        assert!(
            SRC_WH_STEP_MONO_ALL.contains("(wh1 : KExpr -> OptionType KExpr)")
                && SRC_WH_STEP_MONO_ALL.contains("(wh2 : KExpr -> OptionType KExpr)"),
            "step monotonicity must quantify over two arbitrary pre-passes"
        );
        assert!(
            !SRC_WH_STEP_MONO_ALL.contains("whnf_fuel_red_wh"),
            "no fuel-indexed loop should appear in the statement"
        );
    }
}
