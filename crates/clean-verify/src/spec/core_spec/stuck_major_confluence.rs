// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The stuck-major confluence argument: the core, and where it stops.
//!
//! The residual's last open premise needs: a stuck major has no
//! constructor-headed reduct. The route is confluence — the major reduces both
//! to its whnf and to any competing reduct, so they join, and the join's head is
//! pinned from both sides.
//!
//! # Where `i8` enters, and the only place it can
//!
//! `stuck_major_join_ctor_head` consumes `RecEnvCtorNoDefVal` at the
//! **constructor**, keyed on the very `recrule_for` lookup that firing produces.
//! Without it the term does not build — which is exactly right, because the
//! residual is FALSE environment-generically: a name that is both a rule
//! constructor and a def-value carrier would let the competing reduct change its
//! head. `i1..i8` are then discharged in place at `the_red_env`, so the residual
//! does not have to change shape to carry them.
//!
//! # Where it stops, stated so the gap is in the type
//!
//! Classifying the stuck major by its spine head: rigid and lam have no
//! constructor-headed reduct (both preserved forward); `let_` is excluded by
//! stuckness; a delta-dead **recmeta-free** const head likewise. The fourth
//! alternative — a const head **carrying** recmeta — did not close here. There
//! `wmajor` is itself a stuck recursor spine, and the fact needed looked like
//! the residual again, one level down: circular, not merely incomplete.
//!
//! `stuck_major_dead_const_no_ctor_reduct` therefore takes recmeta-freeness as
//! an EXPLICIT hypothesis rather than deriving it, so the circularity is visible
//! rather than buried.
//!
//! **The fourth alternative is now CLOSED** — `stuck_major_recmeta.rs`. The
//! circle is broken by taking `nf_head wmajor` as a premise and having the
//! consumer discharge it from the induction hypothesis at a **strictly smaller
//! budget**, so "one level down" becomes one step of a well-founded recursion
//! rather than a loop. Head identification then goes through
//! `nf_head_star_preserves_const_name`, and `RecEnvCtorNoRecMeta` supplies the
//! contradiction. This file's classification is therefore complete; what
//! remains is the recursion that feeds it.
//!
//! # How the circularity breaks: induct on the BUDGET, not the term
//!
//! `wh3_stuck_at j x` forces the nested pre-pass to run at `j`, and a loop that
//! returns is stuck at a budget **strictly below** its input fuel. So strong
//! induction on the budget should close
//!
//! ```text
//! stuck_head_star_preserved : wh3_stuck_at j x -> x =>* y
//!                               -> const_name (kapp_fn y) = const_name (kapp_fn x)
//! ```
//!
//! and at `j = 0` the recursor-with-filled-slot row is refuted outright, because
//! the nested loop returns `none` and the chain reports `wstarved`, not
//! `wstuck`. **The base case is vacuous because of the three-way split** — the
//! same asymmetry that made the whole wh3 programme possible.
//!
//! That statement would subsume `const_head_star_preserved`,
//! `under_applied_star_preserved` and `bvar_slot_star_preserved`.
//!
//! # Status of the prerequisites — both now in tree
//!
//! The `Lt`-carrying variant this doc asked for is
//! `whnf_fuel_red_wh3_result_stuck_lt` (`budget_induction_prereqs.rs`), and the
//! classification of a `wstuck` verdict is `iota_reduct_whc3_stuck_inv` beside
//! it. Three findings from building them are worth not re-deriving:
//!
//! 1. **The bound really is strict.** It was worth checking rather than
//!    assuming: `Le` would have left the induction with no descent measure.
//!    `wh3_stuck_at` is indexed by the PRE-PASS budget while the loop at fuel
//!    `succ k` evaluates its step against the pre-pass at `k`, so nothing is
//!    ever stuck only at its own input fuel.
//!
//! 2. **The base case needs no separate treatment.** The `j = 0` refutation
//!    described above is already *inside* `whnf_fuel_red_wh3_result_stuck_lt`:
//!    at budget zero the loop returns `none`, so that lemma's own hypothesis is
//!    unsatisfiable and it discharges the row without the caller case-splitting.
//!    The induction is therefore uniform in `k`.
//!
//! 3. **`nat_strong_rec` already exists** (`iota_core.rs`), at a **`Type`**
//!    motive. The predicate here lands in `Prop`, so it needs a Type-valued
//!    box; `Wh3ResultStuck` is the precedent for a Type-valued inductive
//!    carrying a `wh3_stuck_at` field.
//!
//! What remains is the step itself: classify a stuck `x`, and at the late
//! levels feed the pre-pass result to the induction hypothesis at the smaller
//! budget. That is the one open piece, and it is proof engineering rather than
//! an unresolved mathematical question.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The confluence core, the classification, and the visible gap.
    pub(super) fn add_stuck_major_confluence(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            SRC_STUCK_MAJOR_JOIN_CTOR_HEAD,
            "stuck_major_join_ctor_head: THE CONFLUENCE CORE. If the major reduces to wmajor and also to a constructor-headed m2, the common reduct is headed by that same constructor. \\
\\
*** THIS IS WHERE i8 ENTERS, AND IT IS THE ONLY PLACE IT CAN. *** The residual is FALSE environment-generically: a name that is both a rule constructor and a def-value carrier would let m2 change its head under reduction. RecEnvCtorNoDefVal supplies defval_for cname = none, and RecEnvCtorNoRecMeta supplies recmeta_for cname = none, each keyed on the very recrule_for lookup that firing produces. Without i8 this term does not build. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_STUCK_MAJOR_JOIN_CTOR_HEAD_AT_THE_RED_ENV,
            "stuck_major_join_ctor_head_at_the_red_env: the same with i1..i8 discharged in place by the eight checker witnesses. So a discharger of the residual can use the confluence route WITHOUT the residual changing shape to carry them. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_STUCK_MAJOR_RIGID_NO_CTOR_REDUCT,
            "stuck_major_rigid_no_ctor_reduct: a rigid-headed major has no constructor-headed reduct. Rigidity is preserved forward, and a rigid head carries no const name. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_STUCK_MAJOR_LAM_NO_CTOR_REDUCT,
            "stuck_major_lam_no_ctor_reduct: nor does a lambda. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_STUCK_MAJOR_DEAD_CONST_NO_CTOR_REDUCT,
            "stuck_major_dead_const_no_ctor_reduct: the CLOSABLE HALF of the const-headed case — a major whose head is delta-dead AND recmeta-free has no constructor-headed reduct. \\
\\
The recmeta-free hypothesis is taken EXPLICITLY rather than derived, so that the gap is visible in the type instead of buried in a proof. Stuckness gives delta-deadness (wh3_stuck_app_head_no_delta) and says NOTHING about recmeta; when the head does carry recmeta, wmajor is itself a stuck recursor spine and the missing fact is the residual again, one level down. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            SRC_STUCK_MAJOR_NO_CTOR_REDUCT_OF_DEAD_HEAD,
            "stuck_major_no_ctor_reduct_of_dead_head: the dispatcher over a CPS classification of the stuck major. Its fourth alternative — a const head CARRYING recmeta — was the gap; it is now supplied by stuck_major_recmeta_no_ctor_reduct, which breaks the apparent circularity by taking nf_head at the major as a premise that the consumer discharges at a strictly smaller budget. DerivedProved, zero axiom_deps.",
        )?;
        Ok(())
    }
}

const SRC_STUCK_MAJOR_JOIN_CTOR_HEAD: &str = "def stuck_major_join_ctor_head (i1 : RecEnvReductNotRedex (red_rec the_red_env)) (i2 : RecEnvCtorNoRecMeta (red_rec the_red_env)) (i3 : RecEnvClosed (red_rec the_red_env)) (i4 : RecEnvLiftClosed (red_rec the_red_env)) (i5 : DefEnvClosed (red_def the_red_env)) (i6 : DefEnvLiftClosed (red_def the_red_env)) (i7 : RecEnvDefEnvDisjoint the_red_env) (i8 : RecEnvCtorNoDefVal the_red_env) (C : Type) (nm : Name) (cname : Name) (rule : RecRule) (major : KExpr) (wmajor : KExpr) (m2 : KExpr) (hA : par_reduces_cd_star the_red_env major wmajor) (hB : par_reduces_cd_star the_red_env major m2) (hm2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname)) (hrule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule)) (kont : (forall (v : KExpr), par_reduces_cd_star the_red_env wmajor v -> Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname) -> C)) : C := @par_strips_witness_cd_star.rec the_red_env wmajor m2 (fun (_w0 : par_strips_witness_cd_star the_red_env wmajor m2) => C) (fun (v : KExpr) (hwv : par_reduces_cd_star the_red_env wmajor v) (hmv : par_reduces_cd_star the_red_env m2 v) => kont v hwv (const_head_star_preserved the_red_env cname (recenv_ctor_no_defval_cname the_red_env nm cname rule m2 i8 hm2 hrule) (recenv_ctor_no_recmeta_cname (red_rec the_red_env) nm cname rule m2 i2 hm2 hrule) m2 v hmv hm2)) (par_reduces_cd_star_diamond the_red_env i1 i2 i3 i4 i5 i6 i7 i8 major wmajor m2 hA hB)";

const SRC_STUCK_MAJOR_JOIN_CTOR_HEAD_AT_THE_RED_ENV: &str = "def stuck_major_join_ctor_head_at_the_red_env (C : Type) (nm : Name) (cname : Name) (rule : RecRule) (major : KExpr) (wmajor : KExpr) (m2 : KExpr) (hA : par_reduces_cd_star the_red_env major wmajor) (hB : par_reduces_cd_star the_red_env major m2) (hm2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname)) (hrule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule)) (kont : (forall (v : KExpr), par_reduces_cd_star the_red_env wmajor v -> Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname) -> C)) : C := stuck_major_join_ctor_head the_red_env_reduct_not_redex_via_checker the_red_env_ctor_no_recmeta_via_checker the_red_env_rec_closed_via_checker_b2 the_red_env_rec_lift_closed_via_checker_b2 the_red_env_def_closed_via_checker_b2 the_red_env_def_lift_closed_via_checker_b2 the_red_env_defenv_disjoint_via_checker the_red_env_ctor_no_defval_via_checker C nm cname rule major wmajor m2 hA hB hm2 hrule kont";

const SRC_STUCK_MAJOR_RIGID_NO_CTOR_REDUCT: &str = "def stuck_major_rigid_no_ctor_reduct (nm : Name) (cname : Name) (rule : RecRule) (major : KExpr) (wmajor : KExpr) (m2 : KExpr) (hrig : rigid_app_head wmajor) (hA : par_reduces_cd_star the_red_env major wmajor) (hB : par_reduces_cd_star the_red_env major m2) (hm2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname)) (hrule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule)) : Empty := stuck_major_join_ctor_head_at_the_red_env Empty nm cname rule major wmajor m2 hA hB hm2 hrule (fun (v : KExpr) (hwv : par_reduces_cd_star the_red_env wmajor v) (hcv : Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname)) => option_none_ne_some_type Name cname Empty (Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.none Name) (rigid_app_head_no_const v (rigid_app_head_star_preserved the_red_env wmajor v hwv hrig))) hcv))";

const SRC_STUCK_MAJOR_LAM_NO_CTOR_REDUCT: &str = "def stuck_major_lam_no_ctor_reduct (nm : Name) (cname : Name) (rule : RecRule) (major : KExpr) (lty : KExpr) (lb : KExpr) (m2 : KExpr) (hA : par_reduces_cd_star the_red_env major (KExpr.lam lty lb)) (hB : par_reduces_cd_star the_red_env major m2) (hm2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname)) (hrule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule)) : Empty := stuck_major_join_ctor_head_at_the_red_env Empty nm cname rule major (KExpr.lam lty lb) m2 hA hB hm2 hrule (fun (v : KExpr) (hwv : par_reduces_cd_star the_red_env (KExpr.lam lty lb) v) (hcv : Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname)) => par_reduces_cd_star_lam_inv_eq the_red_env lty lb v Empty hwv (fun (ty2 : KExpr) (b2 : KExpr) (heq : Eq KExpr v (KExpr.lam ty2 b2)) (_h1 : par_reduces_cd_star the_red_env lty ty2) (_h2 : par_reduces_cd_star the_red_env lb b2) => option_none_ne_some_type Name cname Empty (Eq.substType KExpr (fun (zz : KExpr) => Eq (OptionType Name) (kexpr_const_name (kapp_fn zz)) (OptionType.some Name cname)) v (KExpr.lam ty2 b2) heq hcv)))";

const SRC_STUCK_MAJOR_DEAD_CONST_NO_CTOR_REDUCT: &str = "def stuck_major_dead_const_no_ctor_reduct (nm : Name) (cname : Name) (cn2 : Name) (rule : RecRule) (major : KExpr) (wmajor : KExpr) (m2 : KExpr) (hwh : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cn2)) (hwdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) cn2) (OptionType.none KExpr)) (hwrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn2) (OptionType.none RecMeta)) (hnorule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cn2) (OptionType.none RecRule)) (hA : par_reduces_cd_star the_red_env major wmajor) (hB : par_reduces_cd_star the_red_env major m2) (hm2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname)) (hrule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule)) : Empty := stuck_major_join_ctor_head_at_the_red_env Empty nm cname rule major wmajor m2 hA hB hm2 hrule (fun (v : KExpr) (hwv : par_reduces_cd_star the_red_env wmajor v) (hcv : Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname)) => option_none_ne_some_type RecRule rule Empty (Eq.trans (OptionType RecRule) (OptionType.none RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule) (Eq.symm (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.none RecRule) (Eq.substType Name (fun (zz : Name) => Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm zz) (OptionType.none RecRule)) cn2 cname (Eq.symm Name cname cn2 (option_some_inj Name cname cn2 (Eq.trans (OptionType Name) (OptionType.some Name cname) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cn2) (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cname) hcv) (const_head_star_preserved the_red_env cn2 hwdef hwrec wmajor v hwv hwh)))) hnorule)) hrule))";

const SRC_STUCK_MAJOR_NO_CTOR_REDUCT_OF_DEAD_HEAD: &str = "def stuck_major_no_ctor_reduct_of_dead_head (nm : Name) (cname : Name) (rule : RecRule) (major : KExpr) (wmajor : KExpr) (m2 : KExpr) (hdead : (forall (D : Type), (rigid_app_head wmajor -> D) -> ((forall (lty : KExpr) (lb : KExpr), Eq KExpr wmajor (KExpr.lam lty lb) -> D)) -> ((forall (cn2 : Name), Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cn2) -> Eq (OptionType KExpr) (defval_for (red_def the_red_env) cn2) (OptionType.none KExpr) -> Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn2) (OptionType.none RecMeta) -> Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cn2) (OptionType.none RecRule) -> D)) -> D)) (hA : par_reduces_cd_star the_red_env major wmajor) (hB : par_reduces_cd_star the_red_env major m2) (hm2 : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cname)) (hrule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cname) (OptionType.some RecRule rule)) : Empty := hdead Empty (fun (hrig : rigid_app_head wmajor) => stuck_major_rigid_no_ctor_reduct nm cname rule major wmajor m2 hrig hA hB hm2 hrule) (fun (lty : KExpr) (lb : KExpr) (heq : Eq KExpr wmajor (KExpr.lam lty lb)) => stuck_major_lam_no_ctor_reduct nm cname rule major lty lb m2 (Eq.substType KExpr (fun (zz : KExpr) => par_reduces_cd_star the_red_env major zz) wmajor (KExpr.lam lty lb) heq hA) hB hm2 hrule) (fun (cn2 : Name) (hwh : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cn2)) (hwdef : Eq (OptionType KExpr) (defval_for (red_def the_red_env) cn2) (OptionType.none KExpr)) (hwrec : Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) cn2) (OptionType.none RecMeta)) (hnorule : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cn2) (OptionType.none RecRule)) => stuck_major_dead_const_no_ctor_reduct nm cname cn2 rule major wmajor m2 hwh hwdef hwrec hnorule hA hB hm2 hrule)";
