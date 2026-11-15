// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Outer constructor-spine argument counts survive actual ParCD and star steps.
//!
//! Raw dead-head facts are premises of the generic core, then DERIVED for rule
//! constructors using faithful i2/i8 disjointness. This is not a typing theorem,
//! source-refinement claim, or arbitrary-spine assertion. Registered with the
//! constant-head immunity primitives; the competing-reduction corollaries in
//! stuck_major_confluence consume both legs of an actual diamond.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (
        r"def const_spine_length_preserved_cd (env : RedEnv) (nm : Name)
 (hdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr))
 (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) (OptionType.none RecMeta))
 (e : KExpr) (e2 : KExpr) (h : par_reduces_cd env e e2) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) :
 Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2)) :=
 LiftP.rec (Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))) (fun (_ : LiftP (Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2)))) => Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))) (fun (hl : Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))) => hl) (par_reduces_cd.rec env
  (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd env x y) => Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args x)) (list_length (kapp_args y))))
  (fun (x : KExpr) (_hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm)) => LiftP.up (Eq Nat (list_length (kapp_args x)) (list_length (kapp_args x))) (Eq.refl Nat (list_length (kapp_args x))))
  (fun (A : KExpr) (A2 : KExpr) (body : KExpr) (body2 : KExpr) (arg : KExpr) (arg2 : KExpr)
   (_hA : par_reduces_cd env A A2) (_hbody : par_reduces_cd env body body2) (_harg : par_reduces_cd env arg arg2)
   (ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args A)) (list_length (kapp_args A2)))) (ihbody : Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args body)) (list_length (kapp_args body2)))) (iharg : Eq (OptionType Name) (kexpr_const_name (kapp_fn arg)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args arg)) (list_length (kapp_args arg2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (OptionType.some Name nm)) =>
   option_none_ne_some_type Name nm (LiftP (Eq Nat (list_length (kapp_args (KExpr.app (KExpr.lam A body) arg))) (list_length (kapp_args (instantiate body2 arg2))))) hh)
  (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr)
   (_hf : par_reduces_cd env f f2) (_ha : par_reduces_cd env a a2)
   (ihf : Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args f)) (list_length (kapp_args f2)))) (iha : Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args a)) (list_length (kapp_args a2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (OptionType.some Name nm)) =>
   LiftP.up (Eq Nat (list_length (kapp_args (KExpr.app f a))) (list_length (kapp_args (KExpr.app f2 a2))))
    (Eq.trans Nat (list_length (kapp_args (KExpr.app f a))) (Nat.succ (list_length (kapp_args f))) (list_length (kapp_args (KExpr.app f2 a2)))
      (list_length_append_singleton (kapp_args f) a)
      (Eq.trans Nat (Nat.succ (list_length (kapp_args f))) (Nat.succ (list_length (kapp_args f2))) (list_length (kapp_args (KExpr.app f2 a2)))
        (Eq.cong Nat Nat Nat.succ (list_length (kapp_args f)) (list_length (kapp_args f2)) (LiftP.rec (Eq Nat (list_length (kapp_args f)) (list_length (kapp_args f2))) (fun (_ : LiftP (Eq Nat (list_length (kapp_args f)) (list_length (kapp_args f2)))) => Eq Nat (list_length (kapp_args f)) (list_length (kapp_args f2))) (fun (hl : Eq Nat (list_length (kapp_args f)) (list_length (kapp_args f2))) => hl) (ihf hh)))
        (Eq.symm Nat (list_length (kapp_args (KExpr.app f2 a2))) (Nat.succ (list_length (kapp_args f2)))
          (list_length_append_singleton (kapp_args f2) a2)))))
  (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr)
   (_hA : par_reduces_cd env A A2) (_hb : par_reduces_cd env b b2)
   (ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args A)) (list_length (kapp_args A2)))) (ihb : Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args b)) (list_length (kapp_args b2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam A b))) (OptionType.some Name nm)) =>
   option_none_ne_some_type Name nm (LiftP (Eq Nat (list_length (kapp_args (KExpr.lam A b))) (list_length (kapp_args (KExpr.lam A2 b2))))) hh)
  (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr)
   (_hA : par_reduces_cd env A A2) (_hb : par_reduces_cd env b b2)
   (ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args A)) (list_length (kapp_args A2)))) (ihb : Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args b)) (list_length (kapp_args b2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi A b))) (OptionType.some Name nm)) =>
   option_none_ne_some_type Name nm (LiftP (Eq Nat (list_length (kapp_args (KExpr.pi A b))) (list_length (kapp_args (KExpr.pi A2 b2))))) hh)
  (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr)
   (_hA : par_reduces_cd env A A2) (_hb : par_reduces_cd env b b2)
   (ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args A)) (list_length (kapp_args A2)))) (ihb : Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args b)) (list_length (kapp_args b2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ A b))) (OptionType.some Name nm)) =>
   option_none_ne_some_type Name nm (LiftP (Eq Nat (list_length (kapp_args (KExpr.forall_ A b))) (list_length (kapp_args (KExpr.forall_ A2 b2))))) hh)
  (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
   (_hA : par_reduces_cd env A A2) (_hv : par_reduces_cd env v v2) (_hb : par_reduces_cd env b b2)
   (ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args A)) (list_length (kapp_args A2)))) (ihv : Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args v)) (list_length (kapp_args v2)))) (ihb : Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args b)) (list_length (kapp_args b2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ A v b))) (OptionType.some Name nm)) =>
   option_none_ne_some_type Name nm (LiftP (Eq Nat (list_length (kapp_args (KExpr.let_ A v b))) (list_length (kapp_args (instantiate b2 v2))))) hh)
  (fun (x : KExpr) (y : KExpr) (hs : iota_step (red_rec env) x y) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm)) =>
  iota_step_no_recmeta_absurd (red_rec env) x y nm (LiftP (Eq Nat (list_length (kapp_args x)) (list_length (kapp_args y)))) hh hrec hs)
  (fun (x : KExpr) (y : KExpr) (hs : delta_step (red_def env) x y) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm)) =>
  option_none_ne_some_type KExpr y (LiftP (Eq Nat (list_length (kapp_args x)) (list_length (kapp_args y))))
   (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (delta_reduct (red_def env) x)
    (OptionType.some KExpr y)
    (Eq.symm (OptionType KExpr) (delta_reduct (red_def env) x) (OptionType.none KExpr)
     (delta_reduct_eq_none_of_defval_none (red_def env) x nm hh hdef)) hs))
  (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
   (_hA : par_reduces_cd env A A2) (_hv : par_reduces_cd env v v2) (_hb : par_reduces_cd env b b2)
   (ihA : Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args A)) (list_length (kapp_args A2)))) (ihv : Eq (OptionType Name) (kexpr_const_name (kapp_fn v)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args v)) (list_length (kapp_args v2)))) (ihb : Eq (OptionType Name) (kexpr_const_name (kapp_fn b)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args b)) (list_length (kapp_args b2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ A v b))) (OptionType.some Name nm)) =>
   option_none_ne_some_type Name nm (LiftP (Eq Nat (list_length (kapp_args (KExpr.let_ A v b))) (list_length (kapp_args (KExpr.let_ A2 v2 b2))))) hh)
  (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr)
   (_hsub : par_reduces_cd env sub sub2)
   (ihsub : Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args sub)) (list_length (kapp_args sub2))))
   (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj sn i sub))) (OptionType.some Name nm)) =>
   option_none_ne_some_type Name nm (LiftP (Eq Nat (list_length (kapp_args (KExpr.proj sn i sub))) (list_length (kapp_args (KExpr.proj sn i sub2))))) hh)
  e e2 h hh)",
        "Actual eleven-arm ParCD induction. Application preserves the outer argument count even when its arguments reduce internally; raw dead-head premises refute both operational head contractions.",
    ),
    (
        r"def const_spine_length_star_preserved (env : RedEnv) (nm : Name)
 (hdef : Eq (OptionType KExpr) (defval_for (red_def env) nm) (OptionType.none KExpr))
 (hrec : Eq (OptionType RecMeta) (recmeta_for (red_rec env) nm) (OptionType.none RecMeta))
 (e : KExpr) (e2 : KExpr) (h : par_reduces_cd_star env e e2) (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name nm)) :
 Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2)) :=
 LiftP.rec (Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))) (fun (_ : LiftP (Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2)))) => Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))) (fun (hl : Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))) => hl) (par_reduces_cd_star.rec env
  (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd_star env x y) => Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args x)) (list_length (kapp_args y))))
  (fun (x : KExpr) (_hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm)) => LiftP.up (Eq Nat (list_length (kapp_args x)) (list_length (kapp_args x))) (Eq.refl Nat (list_length (kapp_args x))))
  (fun (x : KExpr) (y : KExpr) (z : KExpr)
    (hs : par_reduces_cd env x y) (_ht : par_reduces_cd_star env y z)
    (ih : Eq (OptionType Name) (kexpr_const_name (kapp_fn y)) (OptionType.some Name nm) -> LiftP (Eq Nat (list_length (kapp_args y)) (list_length (kapp_args z)))) (hx : Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (OptionType.some Name nm)) =>
    LiftP.up (Eq Nat (list_length (kapp_args x)) (list_length (kapp_args z)))
     (Eq.trans Nat (list_length (kapp_args x)) (list_length (kapp_args y)) (list_length (kapp_args z))
       (const_spine_length_preserved_cd env nm hdef hrec x y hs hx)
       (LiftP.rec (Eq Nat (list_length (kapp_args y)) (list_length (kapp_args z))) (fun (_ : LiftP (Eq Nat (list_length (kapp_args y)) (list_length (kapp_args z)))) => Eq Nat (list_length (kapp_args y)) (list_length (kapp_args z))) (fun (hl : Eq Nat (list_length (kapp_args y)) (list_length (kapp_args z))) => hl) (ih (const_head_preserved_cd env nm hdef hrec x y hs hx)))))
  e e2 h hh)",
        "Actual star induction, carrying the name guard through the existing one-step head theorem and composing proved one-step count equalities.",
    ),
    (
        r"def ctor_spine_length_preserved_cd (env : RedEnv) (faithful : RedEnvFaithful env)
 (recname : Name) (cname : Name) (rule : RecRule) (e : KExpr) (e2 : KExpr)
 (h : par_reduces_cd env e e2)
 (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name cname))
 (hrule : Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule)) :
 Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2)) :=
 const_spine_length_preserved_cd env cname
  (recenv_ctor_no_defval_cname env recname cname rule e (redenv_faithful_i8 env faithful) hh hrule)
  (recenv_ctor_no_recmeta_cname (red_rec env) recname cname rule e (redenv_faithful_i2 env faithful) hh hrule)
  e e2 h hh",
        "Constructor wrapper derives raw name disjointness from the same successful rule lookup and the genuine faithful environment interfaces. No output-length equality is assumed.",
    ),
    (
        r"def ctor_spine_length_preserved_star (env : RedEnv) (faithful : RedEnvFaithful env)
 (recname : Name) (cname : Name) (rule : RecRule) (e : KExpr) (e2 : KExpr)
 (h : par_reduces_cd_star env e e2)
 (hh : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name cname))
 (hrule : Eq (OptionType RecRule) (recrule_for (red_rec env) recname cname) (OptionType.some RecRule rule)) :
 Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2)) :=
 const_spine_length_star_preserved env cname
  (recenv_ctor_no_defval_cname env recname cname rule e (redenv_faithful_i8 env faithful) hh hrule)
  (recenv_ctor_no_recmeta_cname (red_rec env) recname cname rule e (redenv_faithful_i2 env faithful) hh hrule)
  e e2 h hh",
        "Constructor wrapper derives raw name disjointness from the same successful rule lookup and the genuine faithful environment interfaces. No output-length equality is assumed.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def ctor_spine_test_head : KExpr := KExpr.const (Name.str Name.anonymous (Nat.succ Nat.zero)) (ListType.nil Level)",
        "Actual constructor name of the existing faithful environment fixture.",
    ),
    (
        r"def ctor_spine_test_before : KExpr := KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort (Level.succ Level.zero))",
        "A reducible argument; outer constructor-spine count must not count this inner beta spine.",
    ),
    (
        r"def ctor_spine_test_after : KExpr := KExpr.sort (Level.succ Level.zero)",
        "Actual beta result.",
    ),
    (
        r"def ctor_spine_test_source : KExpr := KExpr.app (KExpr.app ctor_spine_test_head ctor_spine_test_before) ctor_spine_test_before",
        "Two outer constructor arguments, each containing a beta redex.",
    ),
    (
        r"def ctor_spine_test_middle : KExpr := KExpr.app (KExpr.app ctor_spine_test_head ctor_spine_test_after) ctor_spine_test_before",
        "First step contracts only the first argument.",
    ),
    (
        r"def ctor_spine_test_target : KExpr := KExpr.app (KExpr.app ctor_spine_test_head ctor_spine_test_after) ctor_spine_test_after",
        "Second step contracts the other argument; both outer slots remain.",
    ),
    (
        r"def ctor_spine_test_beta : par_reduces_cd faithful_red_env ctor_spine_test_before ctor_spine_test_after :=
 par_reduces_cd.beta faithful_red_env (KExpr.sort Level.zero) (KExpr.sort Level.zero)
  (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)
  (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (par_reduces_cd.refl faithful_red_env (KExpr.sort Level.zero))
  (par_reduces_cd.refl faithful_red_env (KExpr.bvar Nat.zero))
  (par_reduces_cd.refl faithful_red_env (KExpr.sort (Level.succ Level.zero)))",
        "Actual nonidentity beta derivation, not an assumed reduction premise.",
    ),
    (
        r"def ctor_spine_test_first : par_reduces_cd faithful_red_env ctor_spine_test_source ctor_spine_test_middle :=
 par_reduces_cd.app faithful_red_env
  (KExpr.app ctor_spine_test_head ctor_spine_test_before) (KExpr.app ctor_spine_test_head ctor_spine_test_after)
  ctor_spine_test_before ctor_spine_test_before
  (par_reduces_cd.app faithful_red_env ctor_spine_test_head ctor_spine_test_head
    ctor_spine_test_before ctor_spine_test_after
    (par_reduces_cd.refl faithful_red_env ctor_spine_test_head) ctor_spine_test_beta)
  (par_reduces_cd.refl faithful_red_env ctor_spine_test_before)",
        "Congruence contracts inside the first outer slot.",
    ),
    (
        r"def ctor_spine_test_second : par_reduces_cd faithful_red_env ctor_spine_test_middle ctor_spine_test_target :=
 par_reduces_cd.app faithful_red_env
  (KExpr.app ctor_spine_test_head ctor_spine_test_after) (KExpr.app ctor_spine_test_head ctor_spine_test_after)
  ctor_spine_test_before ctor_spine_test_after
  (par_reduces_cd.refl faithful_red_env (KExpr.app ctor_spine_test_head ctor_spine_test_after))
  ctor_spine_test_beta",
        "Congruence contracts inside the second outer slot.",
    ),
    (
        r"def ctor_spine_test_trace : par_reduces_cd_star faithful_red_env ctor_spine_test_source ctor_spine_test_target :=
 par_reduces_cd_star.step faithful_red_env ctor_spine_test_source ctor_spine_test_middle ctor_spine_test_target
  ctor_spine_test_first
  (par_reduces_cd_star.step faithful_red_env ctor_spine_test_middle ctor_spine_test_target ctor_spine_test_target
    ctor_spine_test_second (par_reduces_cd_star.refl faithful_red_env ctor_spine_test_target))",
        "Genuine two-link star trace with different slots contracted in sequence.",
    ),
    (
        r"def ctor_spine_test_rule : RecRule :=
 RecRule.mk (Name.str Name.anonymous (Nat.succ Nat.zero)) Nat.zero
  (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero))",
        "The actual stored rule of the existing faithful fixture.",
    ),
    (
        r"def ctor_spine_test_lookup :
 Eq (OptionType RecRule)
  (recrule_for (red_rec faithful_red_env) (Name.str Name.anonymous Nat.zero) (Name.str Name.anonymous (Nat.succ Nat.zero)))
  (OptionType.some RecRule ctor_spine_test_rule) :=
 Eq.refl (OptionType RecRule) (OptionType.some RecRule ctor_spine_test_rule)",
        "Actual lookup computes; constructor membership is not assumed.",
    ),
    (
        r"def ctor_spine_test_one_count :
 Eq Nat (list_length (kapp_args ctor_spine_test_source)) (list_length (kapp_args ctor_spine_test_middle)) :=
 ctor_spine_length_preserved_cd faithful_red_env faithful_red_env_faithful
  (Name.str Name.anonymous Nat.zero) (Name.str Name.anonymous (Nat.succ Nat.zero))
  ctor_spine_test_rule ctor_spine_test_source ctor_spine_test_middle ctor_spine_test_first
  (Eq.refl (OptionType Name) (OptionType.some Name (Name.str Name.anonymous (Nat.succ Nat.zero))))
  ctor_spine_test_lookup",
        "Actual one-step caller uses discharged faithful disjointness.",
    ),
    (
        r"def ctor_spine_test_star_count :
 Eq Nat (list_length (kapp_args ctor_spine_test_source)) (list_length (kapp_args ctor_spine_test_target)) :=
 ctor_spine_length_preserved_star faithful_red_env faithful_red_env_faithful
  (Name.str Name.anonymous Nat.zero) (Name.str Name.anonymous (Nat.succ Nat.zero))
  ctor_spine_test_rule ctor_spine_test_source ctor_spine_test_target ctor_spine_test_trace
  (Eq.refl (OptionType Name) (OptionType.some Name (Name.str Name.anonymous (Nat.succ Nat.zero))))
  ctor_spine_test_lookup",
        "Actual two-step caller uses both checked trace and actual rule lookup.",
    ),
    (
        r"def ctor_spine_test_exact_length :
 Eq Nat (list_length (kapp_args ctor_spine_test_target)) (Nat.succ (Nat.succ Nat.zero)) :=
 Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))",
        "The preserved count is exactly two, not merely an inhabited equality type.",
    ),
];

impl Specification {
    pub(super) fn add_ctor_spine_lengths(&mut self) -> Result<(), SpecError> {
        for (source, description) in PROOFS {
            self.add_recursive_def(source, description)?;
        }
        for (source, description) in CONTROLS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn constructor_spine_counts_survive_actual_parallel_steps() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            // Works as an unregistered draft and after later stage integration.
            if !spec
                .definitions()
                .contains_key("const_spine_length_preserved_cd")
            {
                spec.add_ctor_spine_lengths()
                    .expect("actual proof terms must check");
            }
            for name in [
                "const_spine_length_preserved_cd",
                "const_spine_length_star_preserved",
                "ctor_spine_length_preserved_cd",
                "ctor_spine_length_preserved_star",
                "ctor_spine_test_beta",
                "ctor_spine_test_first",
                "ctor_spine_test_second",
                "ctor_spine_test_trace",
                "ctor_spine_test_lookup",
                "ctor_spine_test_one_count",
                "ctor_spine_test_star_count",
                "ctor_spine_test_exact_length",
            ] {
                let definition = spec
                    .definitions()
                    .get(name)
                    .expect("actual spine-count result");
                assert!(!definition.is_axiom, "{name}");
                assert!(definition.elaborated_value.is_some(), "{name}");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn constructor_spine_count_rejects_forged_length_and_missing_head_guard() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            if !spec
                .definitions()
                .contains_key("const_spine_length_preserved_cd")
            {
                spec.add_ctor_spine_lengths()
                    .expect("actual proof terms must check");
            }
            for source in [
                r"def ctor_spine_forged_length :
 Eq Nat (list_length (kapp_args ctor_spine_test_target)) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) :=
 Eq.refl Nat (Nat.succ (Nat.succ Nat.zero))",
                r"def ctor_spine_forged_unqualified :
 Eq Nat (list_length (kapp_args ctor_spine_test_before)) (list_length (kapp_args ctor_spine_test_after)) :=
 Eq.refl Nat Nat.zero",
                r"def ctor_spine_forged_head :
 Eq Nat (list_length (kapp_args ctor_spine_test_before)) (list_length (kapp_args ctor_spine_test_after)) :=
 const_spine_length_preserved_cd faithful_red_env (Name.str Name.anonymous (Nat.succ Nat.zero))
  (Eq.refl (OptionType KExpr) (OptionType.none KExpr))
  (Eq.refl (OptionType RecMeta) (OptionType.none RecMeta))
  ctor_spine_test_before ctor_spine_test_after ctor_spine_test_beta
  (Eq.refl (OptionType Name) (OptionType.some Name (Name.str Name.anonymous (Nat.succ Nat.zero))))",
            ] {
                assert!(spec
                    .add_recursive_def(source, "Planted spine-count forgery")
                    .is_err());
            }
        });
    }
}
