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

// The actual diamond supplies BOTH outgoing legs. No nf_head premise or
// caller-supplied equality of constructor-spine lengths is assumed.
const COMPETING_CTOR_PROOFS: &[(&str, &str)] = &[
    (r"def competing_ctor_spine_views (env : RedEnv) (faithful : RedEnvFaithful env)
 (nm : Name) (cnameA : Name) (ruleA : RecRule) (cnameB : Name) (ruleB : RecRule)
 (major : KExpr) (wmajor : KExpr) (m2 : KExpr)
 (hA : par_reduces_cd_star env major wmajor) (hB : par_reduces_cd_star env major m2)
 (headA : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cnameA)) (lookupA : Eq (OptionType RecRule) (recrule_for (red_rec env) nm cnameA) (OptionType.some RecRule ruleA))
 (headB : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cnameB)) (lookupB : Eq (OptionType RecRule) (recrule_for (red_rec env) nm cnameB) (OptionType.some RecRule ruleB))
 (C : Type)
 (kont : Eq Name cnameA cnameB -> Eq RecRule ruleA ruleB ->
   Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2)) -> C) : C :=
 @par_strips_witness_cd_star.rec env wmajor m2
  (fun (_ : par_strips_witness_cd_star env wmajor m2) => C)
  (fun (v : KExpr) (hwv : par_reduces_cd_star env wmajor v)
    (hmv : par_reduces_cd_star env m2 v) =>
    (fun (sameName : Eq Name cnameA cnameB) => kont sameName (option_some_inj RecRule ruleA ruleB
 (Eq.trans (OptionType RecRule) (OptionType.some RecRule ruleA)
  (recrule_for (red_rec env) nm cnameA) (OptionType.some RecRule ruleB)
  (Eq.symm (OptionType RecRule) (recrule_for (red_rec env) nm cnameA) (OptionType.some RecRule ruleA) lookupA)
  (Eq.trans (OptionType RecRule) (recrule_for (red_rec env) nm cnameA)
   (recrule_for (red_rec env) nm cnameB) (OptionType.some RecRule ruleB)
   (Eq.cong Name (OptionType RecRule) (fun (cname : Name) => recrule_for (red_rec env) nm cname) cnameA cnameB sameName)
   lookupB))) (Eq.trans Nat (list_length (kapp_args wmajor)) (list_length (kapp_args v)) (list_length (kapp_args m2))
 (ctor_spine_length_preserved_star env faithful nm cnameA ruleA wmajor v hwv headA lookupA)
 (Eq.symm Nat (list_length (kapp_args m2)) (list_length (kapp_args v))
  (ctor_spine_length_preserved_star env faithful nm cnameB ruleB m2 v hmv headB lookupB)))) (option_some_inj Name cnameA cnameB
 (Eq.trans (OptionType Name) (OptionType.some Name cnameA) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cnameB)
  (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name cnameA) (const_head_star_preserved env cnameA
 (recenv_ctor_no_defval_cname env nm cnameA ruleA wmajor (redenv_faithful_i8 env faithful) headA lookupA)
 (recenv_ctor_no_recmeta_cname (red_rec env) nm cnameA ruleA wmajor (redenv_faithful_i2 env faithful) headA lookupA)
 wmajor v hwv headA))
  (const_head_star_preserved env cnameB
 (recenv_ctor_no_defval_cname env nm cnameB ruleB m2 (redenv_faithful_i8 env faithful) headB lookupB)
 (recenv_ctor_no_recmeta_cname (red_rec env) nm cnameB ruleB m2 (redenv_faithful_i2 env faithful) headB lookupB)
 m2 v hmv headB))))
  (par_reduces_cd_star_diamond env (redenv_faithful_i1 env faithful) (redenv_faithful_i2 env faithful) (redenv_faithful_i3 env faithful) (redenv_faithful_i4 env faithful) (redenv_faithful_i5 env faithful) (redenv_faithful_i6 env faithful) (redenv_faithful_i7 env faithful) (redenv_faithful_i8 env faithful) major wmajor m2 hA hB)", "Retain both actual diamond legs; faithful constructor heads and functional rule lookup align names/rules, while proved constructor-spine preservation aligns lengths."),
    (r"def competing_ctor_spine_length (env : RedEnv) (faithful : RedEnvFaithful env)
 (nm : Name) (cnameA : Name) (ruleA : RecRule) (cnameB : Name) (ruleB : RecRule)
 (major : KExpr) (wmajor : KExpr) (m2 : KExpr)
 (hA : par_reduces_cd_star env major wmajor) (hB : par_reduces_cd_star env major m2)
 (headA : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cnameA)) (lookupA : Eq (OptionType RecRule) (recrule_for (red_rec env) nm cnameA) (OptionType.some RecRule ruleA))
 (headB : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cnameB)) (lookupB : Eq (OptionType RecRule) (recrule_for (red_rec env) nm cnameB) (OptionType.some RecRule ruleB)) : Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2)) :=
 LiftP.rec (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2)))
  (fun (_ : LiftP (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2)))) => (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2))))
  (fun (sameLength : (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2)))) => sameLength)
  (competing_ctor_spine_views env faithful nm cnameA ruleA cnameB ruleB major wmajor m2
    hA hB headA lookupA headB lookupB (LiftP (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2))))
    (fun (_sameName : Eq Name cnameA cnameB) (_sameRule : Eq RecRule ruleA ruleB)
      (sameLength : (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2)))) => LiftP.up (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2))) sameLength))", "Prop-valued corollary of the actual competing constructor-spine view, with no assumed length equality."),
    (r"def stuck_major_fields_short_no_firing
 (nm : Name) (cnameA : Name) (ruleA : RecRule) (major : KExpr) (wmajor : KExpr)
 (hA : par_reduces_cd_star the_red_env major wmajor)
 (headA : Eq (OptionType Name) (kexpr_const_name (kapp_fn wmajor)) (OptionType.some Name cnameA))
 (lookupA : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cnameA) (OptionType.some RecRule ruleA))
 (short : Eq Bool (iota_fields_ok ruleA (kapp_args wmajor)) Bool.false)
 (cnameB : Name) (ruleB : RecRule) (m2 : KExpr)
 (hB : par_reduces_cd_star the_red_env major m2)
 (headB : Eq (OptionType Name) (kexpr_const_name (kapp_fn m2)) (OptionType.some Name cnameB))
 (lookupB : Eq (OptionType RecRule) (recrule_for (red_rec the_red_env) nm cnameB) (OptionType.some RecRule ruleB))
 (fields : Eq Bool (iota_fields_ok ruleB (kapp_args m2)) Bool.true) : Empty :=
 competing_ctor_spine_views the_red_env the_red_env_faithful nm cnameA ruleA cnameB ruleB major wmajor m2
  hA hB headA lookupA headB lookupB Empty
  (fun (_sameName : Eq Name cnameA cnameB) (sameRule : Eq RecRule ruleA ruleB)
    (sameLength : (Eq Nat (list_length (kapp_args wmajor)) (list_length (kapp_args m2)))) =>
   bool_false_ne_true_t Empty
    (Eq.trans Bool Bool.false (iota_fields_ok ruleA (kapp_args wmajor)) Bool.true
      (Eq.symm Bool (iota_fields_ok ruleA (kapp_args wmajor)) Bool.false short)
      (Eq.trans Bool (iota_fields_ok ruleA (kapp_args wmajor)) (iota_fields_ok ruleB (kapp_args m2)) Bool.true (Eq.trans Bool (iota_fields_ok ruleA (kapp_args wmajor)) (iota_fields_ok ruleA (kapp_args m2)) (iota_fields_ok ruleB (kapp_args m2))
 (Eq.cong Nat Bool (fun (count : Nat) => nat_eqb (Nat.sub (recrule_num_fields ruleA) count) Nat.zero) (list_length (kapp_args wmajor)) (list_length (kapp_args m2)) sameLength)
 (Eq.cong RecRule Bool (fun (rule : RecRule) => iota_fields_ok rule (kapp_args m2)) ruleA ruleB sameRule)) fields)))", "At the actual faithful environment, a short-field constructor major rules out sufficient fields at any competing constructor/rule reduct; no nf_head premise."),
    (r"def competing_ctor_spine_actual_trace :
 Eq Nat (list_length (kapp_args ctor_spine_test_middle))
  (list_length (kapp_args ctor_spine_test_target)) :=
 competing_ctor_spine_length faithful_red_env faithful_red_env_faithful
  (Name.str Name.anonymous Nat.zero) (Name.str Name.anonymous (Nat.succ Nat.zero)) ctor_spine_test_rule (Name.str Name.anonymous (Nat.succ Nat.zero)) ctor_spine_test_rule
  ctor_spine_test_source ctor_spine_test_middle ctor_spine_test_target
  (par_reduces_cd_star.step faithful_red_env ctor_spine_test_source ctor_spine_test_middle ctor_spine_test_middle
    ctor_spine_test_first (par_reduces_cd_star.refl faithful_red_env ctor_spine_test_middle))
  ctor_spine_test_trace
  (Eq.refl (OptionType Name) (OptionType.some Name (Name.str Name.anonymous (Nat.succ Nat.zero)))) ctor_spine_test_lookup
  (Eq.refl (OptionType Name) (OptionType.some Name (Name.str Name.anonymous (Nat.succ Nat.zero)))) ctor_spine_test_lookup", "Concrete competing nonidentity traces in the existing faithful fixture; the length corollary consumes actual constructor membership, not a postulated count."),
];

impl Specification {
    /// The confluence core, the classification, and the visible gap.
    pub(super) fn add_stuck_major_confluence(&mut self) -> Result<(), SpecError> {
        for (source, description) in COMPETING_CTOR_PROOFS {
            self.add_recursive_def(source, description)?;
        }
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

#[cfg(test)]
mod competing_ctor_tests {
    use super::*;

    #[test]
    fn competing_ctor_sources_parse_and_retain_both_legs() {
        for (source, _) in COMPETING_CTOR_PROOFS {
            assert!(Specification::balanced(source));
            crate::test_utils::parse_check(source)
                .expect("actual competing-constructor proof parses");
        }
        let views = COMPETING_CTOR_PROOFS[0].0;
        assert!(views.contains("par_reduces_cd_star_diamond env"));
        assert!(views.contains("wmajor v hwv headA lookupA"));
        assert!(views.contains("m2 v hmv headB lookupB"));
        assert!(views.contains("option_some_inj RecRule ruleA ruleB"));
        assert!(!views.contains("nf_head"));
        assert!(COMPETING_CTOR_PROOFS[2]
            .0
            .contains("the_red_env the_red_env_faithful"));
    }

    #[test]
    fn competing_ctor_roots_have_checked_empty_closures() {
        let spec = crate::test_utils::build_spec_with_stack();
        for (source, _) in COMPETING_CTOR_PROOFS {
            let name = source.split_whitespace().nth(1).expect("definition name");
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered competing-constructor proof");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
}
