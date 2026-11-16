// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual CDP-star / CD-or-projection-star derivation inclusions.
//! Exact tuples from cdp-union-sandwich.E9wUsg. Both maps work in arbitrary R
//! without a confluence, closure-equivalence or desired endpoint premise.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "cd_projection_union_star",
        r"forall (R : RedEnv) (e r : KExpr), Type",
        r"fun (R : RedEnv) (e r : KExpr) => RelationStar KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) e r",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_single_cd",
        r"forall (R : RedEnv) (e r : KExpr) (h : par_reduces_cd R e r), cd_projection_union_star R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : par_reduces_cd R e r) => relation_star_single KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) e r (@RelationUnion.left KExpr (par_reduces_cd R) (projection_parallel R) e r h)",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_single_projection",
        r"forall (R : RedEnv) (e r : KExpr) (h : projection_parallel R e r), cd_projection_union_star R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : projection_parallel R e r) => relation_star_single KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) e r (@RelationUnion.right KExpr (par_reduces_cd R) (projection_parallel R) e r h)",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_trans",
        r"forall (R : RedEnv) (e m r : KExpr) (h : cd_projection_union_star R e m) (tail : cd_projection_union_star R m r), cd_projection_union_star R e r",
        r"fun (R : RedEnv) (e m r : KExpr) (h : cd_projection_union_star R e m) (tail : cd_projection_union_star R m r) => relation_star_trans KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) e m r h tail",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_context",
        r"forall (R : RedEnv) (F : KExpr -> KExpr)
(cd_context : forall (x y : KExpr), par_reduces_cd R x y -> par_reduces_cd R (F x) (F y))
(proj : forall (x y : KExpr), projection_parallel R x y -> projection_parallel R (F x) (F y))
(e r : KExpr) (h : cd_projection_union_star R e r), cd_projection_union_star R (F e) (F r)",
        r"fun (R : RedEnv) (F : KExpr -> KExpr)
(cd_context : forall (x y : KExpr), par_reduces_cd R x y -> par_reduces_cd R (F x) (F y))
(proj : forall (x y : KExpr), projection_parallel R x y -> projection_parallel R (F x) (F y))
(e r : KExpr) (h : cd_projection_union_star R e r) => @RelationStar.rec KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R))
 (fun (x y : KExpr) (_h : RelationStar KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) x y) => cd_projection_union_star R (F x) (F y))
 (fun (x : KExpr) => @RelationStar.refl KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) (F x))
 (fun (x y z : KExpr) (xy : RelationUnion KExpr (par_reduces_cd R) (projection_parallel R) x y)
  (_tail : RelationStar KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) y z) (ih : cd_projection_union_star R (F y) (F z)) =>
  @RelationStar.step KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) (F x) (F y) (F z)
   (@RelationUnion.rec KExpr (par_reduces_cd R) (projection_parallel R) x y
    (fun (_edge : RelationUnion KExpr (par_reduces_cd R) (projection_parallel R) x y) =>
     RelationUnion KExpr (par_reduces_cd R) (projection_parallel R) (F x) (F y))
    (fun (hc : par_reduces_cd R x y) =>
     @RelationUnion.left KExpr (par_reduces_cd R) (projection_parallel R) (F x) (F y) (cd_context x y hc))
    (fun (hp : projection_parallel R x y) =>
     @RelationUnion.right KExpr (par_reduces_cd R) (projection_parallel R) (F x) (F y) (proj x y hp)) xy) ih)
 e r h",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_app",
        r"forall (R : RedEnv) (f f2 a a2 : KExpr)
 (hf : cd_projection_union_star R f f2) (ha : cd_projection_union_star R a a2), cd_projection_union_star R (KExpr.app f a) (KExpr.app f2 a2)",
        r"fun (R : RedEnv) (f f2 a a2 : KExpr)
 (hf : cd_projection_union_star R f f2) (ha : cd_projection_union_star R a a2) => cd_projection_union_star_trans R (KExpr.app f a) (KExpr.app f2 a) (KExpr.app f2 a2)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.app x a))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.app R x y a a h (@par_reduces_cd.refl R a))
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.app R x y a a h (@projection_parallel.refl R a))
   f f2 hf)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.app f2 x))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.app R f2 f2 x y (@par_reduces_cd.refl R f2) h)
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.app R f2 f2 x y (@projection_parallel.refl R f2) h)
   a a2 ha)",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_lam",
        r"forall (R : RedEnv) (A A2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (hb : cd_projection_union_star R b b2), cd_projection_union_star R (KExpr.lam A b) (KExpr.lam A2 b2)",
        r"fun (R : RedEnv) (A A2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (hb : cd_projection_union_star R b b2) => cd_projection_union_star_trans R (KExpr.lam A b) (KExpr.lam A2 b) (KExpr.lam A2 b2)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.lam x b))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.lam R x y b b h (@par_reduces_cd.refl R b))
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.lam R x y b b h (@projection_parallel.refl R b))
   A A2 hA)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.lam A2 x))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.lam R A2 A2 x y (@par_reduces_cd.refl R A2) h)
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.lam R A2 A2 x y (@projection_parallel.refl R A2) h)
   b b2 hb)",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_pi",
        r"forall (R : RedEnv) (A A2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (hb : cd_projection_union_star R b b2), cd_projection_union_star R (KExpr.pi A b) (KExpr.pi A2 b2)",
        r"fun (R : RedEnv) (A A2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (hb : cd_projection_union_star R b b2) => cd_projection_union_star_trans R (KExpr.pi A b) (KExpr.pi A2 b) (KExpr.pi A2 b2)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.pi x b))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.pi R x y b b h (@par_reduces_cd.refl R b))
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.pi R x y b b h (@projection_parallel.refl R b))
   A A2 hA)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.pi A2 x))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.pi R A2 A2 x y (@par_reduces_cd.refl R A2) h)
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.pi R A2 A2 x y (@projection_parallel.refl R A2) h)
   b b2 hb)",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_forall_",
        r"forall (R : RedEnv) (A A2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (hb : cd_projection_union_star R b b2), cd_projection_union_star R (KExpr.forall_ A b) (KExpr.forall_ A2 b2)",
        r"fun (R : RedEnv) (A A2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (hb : cd_projection_union_star R b b2) => cd_projection_union_star_trans R (KExpr.forall_ A b) (KExpr.forall_ A2 b) (KExpr.forall_ A2 b2)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.forall_ x b))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.forall_ R x y b b h (@par_reduces_cd.refl R b))
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.forall_ R x y b b h (@projection_parallel.refl R b))
   A A2 hA)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.forall_ A2 x))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.forall_ R A2 A2 x y (@par_reduces_cd.refl R A2) h)
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.forall_ R A2 A2 x y (@projection_parallel.refl R A2) h)
   b b2 hb)",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_let_cong",
        r"forall (R : RedEnv) (A A2 a a2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (ha : cd_projection_union_star R a a2) (hb : cd_projection_union_star R b b2), cd_projection_union_star R (KExpr.let_ A a b) (KExpr.let_ A2 a2 b2)",
        r"fun (R : RedEnv) (A A2 a a2 b b2 : KExpr)
 (hA : cd_projection_union_star R A A2) (ha : cd_projection_union_star R a a2) (hb : cd_projection_union_star R b b2) => cd_projection_union_star_trans R (KExpr.let_ A a b) (KExpr.let_ A2 a b) (KExpr.let_ A2 a2 b2)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.let_ x a b))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.let_cong R x y a a b b h (@par_reduces_cd.refl R a) (@par_reduces_cd.refl R b))
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.let_cong R x y a a b b h (@projection_parallel.refl R a) (@projection_parallel.refl R b))
   A A2 hA)
  (cd_projection_union_star_trans R (KExpr.let_ A2 a b) (KExpr.let_ A2 a2 b) (KExpr.let_ A2 a2 b2)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.let_ A2 x b))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.let_cong R A2 A2 x y b b (@par_reduces_cd.refl R A2) h (@par_reduces_cd.refl R b))
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.let_cong R A2 A2 x y b b (@projection_parallel.refl R A2) h (@projection_parallel.refl R b))
   a a2 ha)
  (cd_projection_union_star_context R (fun (x : KExpr) => (KExpr.let_ A2 a2 x))
   (fun (x y : KExpr) (h : par_reduces_cd R x y) => @par_reduces_cd.let_cong R A2 A2 a2 a2 x y (@par_reduces_cd.refl R A2) (@par_reduces_cd.refl R a2) h)
   (fun (x y : KExpr) (h : projection_parallel R x y) => @projection_parallel.let_cong R A2 A2 a2 a2 x y (@projection_parallel.refl R A2) (@projection_parallel.refl R a2) h)
   b b2 hb))",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_proj",
        r"forall (R : RedEnv) (S : Name) (idx : Nat) (e r : KExpr) (h : cd_projection_union_star R e r), cd_projection_union_star R (KExpr.proj S idx e) (KExpr.proj S idx r)",
        r"fun (R : RedEnv) (S : Name) (idx : Nat) (e r : KExpr) (h : cd_projection_union_star R e r) => cd_projection_union_star_context R (fun (x : KExpr) => KExpr.proj S idx x)
 (fun (x y : KExpr) (step : par_reduces_cd R x y) => @par_reduces_cd.proj R S idx x y step)
 (fun (x y : KExpr) (step : projection_parallel R x y) => @projection_parallel.proj R S idx x y step)
 e r h",
    ),
    DeclarationInput::Proof(
        "cdp_to_cd_projection_union_star",
        r"forall (R : RedEnv) (e r : KExpr) (h : par_reduces_cdp R e r), cd_projection_union_star R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : par_reduces_cdp R e r) => @par_reduces_cdp.rec R (fun (x y : KExpr) (_h : par_reduces_cdp R x y) => cd_projection_union_star R x y)
 (fun (x : KExpr) => @RelationStar.refl KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) x)
 (fun (A A2 b b2 a a2 : KExpr)
 (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2) (_ha : par_reduces_cdp R a a2)
 (ihA : cd_projection_union_star R A A2) (ihb : cd_projection_union_star R b b2) (iha : cd_projection_union_star R a a2) =>
 cd_projection_union_star_trans R
 (KExpr.app (KExpr.lam A b) a) (KExpr.app (KExpr.lam A2 b2) a2) (instantiate b2 a2)
 (cd_projection_union_star_app R (KExpr.lam A b) (KExpr.lam A2 b2) a a2
  (cd_projection_union_star_lam R A A2 b b2 ihA ihb) iha)
 (cd_projection_union_star_single_cd R (KExpr.app (KExpr.lam A2 b2) a2) (instantiate b2 a2)
  (@par_reduces_cd.beta R A2 A2 b2 b2 a2 a2
   (@par_reduces_cd.refl R A2) (@par_reduces_cd.refl R b2) (@par_reduces_cd.refl R a2))))
 (fun (f f2 a a2 : KExpr)
 (_hf : par_reduces_cdp R f f2) (_ha : par_reduces_cdp R a a2)
 (ihf : cd_projection_union_star R f f2) (iha : cd_projection_union_star R a a2) =>
 cd_projection_union_star_app R f f2 a a2 ihf iha)
 (fun (A A2 b b2 : KExpr)
 (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2)
 (ihA : cd_projection_union_star R A A2) (ihb : cd_projection_union_star R b b2) =>
 cd_projection_union_star_lam R A A2 b b2 ihA ihb)
 (fun (A A2 b b2 : KExpr)
 (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2)
 (ihA : cd_projection_union_star R A A2) (ihb : cd_projection_union_star R b b2) =>
 cd_projection_union_star_pi R A A2 b b2 ihA ihb)
 (fun (A A2 b b2 : KExpr)
 (_hA : par_reduces_cdp R A A2) (_hb : par_reduces_cdp R b b2)
 (ihA : cd_projection_union_star R A A2) (ihb : cd_projection_union_star R b b2) =>
 cd_projection_union_star_forall_ R A A2 b b2 ihA ihb)
 (fun (A A2 a a2 b b2 : KExpr)
 (_hA : par_reduces_cdp R A A2) (_ha : par_reduces_cdp R a a2) (_hb : par_reduces_cdp R b b2)
 (ihA : cd_projection_union_star R A A2) (iha : cd_projection_union_star R a a2) (ihb : cd_projection_union_star R b b2) =>
 cd_projection_union_star_trans R
 (KExpr.let_ A a b) (KExpr.let_ A2 a2 b2) (instantiate b2 a2)
 (cd_projection_union_star_let_cong R A A2 a a2 b b2 ihA iha ihb)
 (cd_projection_union_star_single_cd R (KExpr.let_ A2 a2 b2) (instantiate b2 a2)
  (@par_reduces_cd.let_ R A2 A2 a2 a2 b2 b2
   (@par_reduces_cd.refl R A2) (@par_reduces_cd.refl R a2) (@par_reduces_cd.refl R b2))))
 (fun (x y : KExpr) (step : iota_step (red_rec R) x y) => cd_projection_union_star_single_cd R x y (@par_reduces_cd.iota R x y step))
 (fun (x y : KExpr) (step : delta_step (red_def R) x y) => cd_projection_union_star_single_cd R x y (@par_reduces_cd.delta R x y step))
 (fun (A A2 a a2 b b2 : KExpr)
 (_hA : par_reduces_cdp R A A2) (_ha : par_reduces_cdp R a a2) (_hb : par_reduces_cdp R b b2)
 (ihA : cd_projection_union_star R A A2) (iha : cd_projection_union_star R a a2) (ihb : cd_projection_union_star R b b2) =>
 cd_projection_union_star_let_cong R A A2 a a2 b b2 ihA iha ihb)
 (fun (S : Name) (idx : Nat) (x y : KExpr) (_step : par_reduces_cdp R x y) (ih : cd_projection_union_star R x y) => cd_projection_union_star_proj R S idx x y ih)
 (fun (S : Name) (idx : Nat) (subject result : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr result)) =>
 cd_projection_union_star_single_projection R (KExpr.proj S idx subject) result
  (@projection_parallel.projection_beta R S idx subject result run))
 e r h",
    ),
    DeclarationInput::Proof(
        "cdp_star_to_cd_projection_union_star",
        r"forall (R : RedEnv) (e r : KExpr) (h : par_reduces_cdp_star R e r), cd_projection_union_star R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : par_reduces_cdp_star R e r) => @par_reduces_cdp_star.rec R
 (fun (x y : KExpr) (_h : par_reduces_cdp_star R x y) => cd_projection_union_star R x y)
 (fun (x : KExpr) => @RelationStar.refl KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) x)
 (fun (x y z : KExpr) (xy : par_reduces_cdp R x y) (_tail : par_reduces_cdp_star R y z)
  (ih : cd_projection_union_star R y z) =>
  cd_projection_union_star_trans R x y z (cdp_to_cd_projection_union_star R x y xy) ih)
 e r h",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_to_cdp",
        r"forall (R : RedEnv) (e r : KExpr) (h : RelationUnion KExpr (par_reduces_cd R) (projection_parallel R) e r), par_reduces_cdp R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : RelationUnion KExpr (par_reduces_cd R) (projection_parallel R) e r) => @RelationUnion.rec KExpr (par_reduces_cd R) (projection_parallel R) e r
 (fun (_h : RelationUnion KExpr (par_reduces_cd R) (projection_parallel R) e r) => par_reduces_cdp R e r)
 (fun (cd_edge : par_reduces_cd R e r) => par_reduces_cd_to_cdp R e r cd_edge)
 (fun (proj : projection_parallel R e r) => projection_parallel_to_cdp R e r proj) h",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_to_cdp_star",
        r"forall (R : RedEnv) (e r : KExpr) (h : cd_projection_union_star R e r), par_reduces_cdp_star R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : cd_projection_union_star R e r) => @RelationStar.rec KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R))
 (fun (x y : KExpr) (_h : RelationStar KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) x y) => par_reduces_cdp_star R x y)
 (fun (x : KExpr) => @par_reduces_cdp_star.refl R x)
 (fun (x y z : KExpr) (xy : RelationUnion KExpr (par_reduces_cd R) (projection_parallel R) x y)
  (_tail : RelationStar KExpr (RelationUnion KExpr (par_reduces_cd R) (projection_parallel R)) y z) (ih : par_reduces_cdp_star R y z) =>
  @par_reduces_cdp_star.step R x y z (cd_projection_union_to_cdp R x y xy) ih)
 e r h",
    ),
    DeclarationInput::Data(
        "cdp_union_mixed_source",
        r"KExpr",
        r"KExpr.app (KExpr.lam rfnz_nat cdp_binding_projection) (KExpr.bvar (Nat.succ Nat.zero))",
    ),
    DeclarationInput::Data(
        "cdp_union_mixed_middle",
        r"KExpr",
        r"KExpr.app (KExpr.lam rfnz_nat projection_binding_field) (KExpr.bvar (Nat.succ Nat.zero))",
    ),
    DeclarationInput::Proof(
        "cdp_union_mixed_projection_leg",
        r"projection_parallel the_red_env cdp_union_mixed_source cdp_union_mixed_middle",
        r"@projection_parallel.app the_red_env
  (KExpr.lam rfnz_nat cdp_binding_projection) (KExpr.lam rfnz_nat projection_binding_field)
  (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero))
  (@projection_parallel.lam the_red_env rfnz_nat rfnz_nat cdp_binding_projection projection_binding_field
   (@projection_parallel.refl the_red_env rfnz_nat)
   (@projection_parallel.projection_beta the_red_env kcre_prod_type_name Nat.zero
    projection_binding_subject projection_binding_field projection_binding_select))
  (@projection_parallel.refl the_red_env (KExpr.bvar (Nat.succ Nat.zero)))",
    ),
    DeclarationInput::Proof(
        "cdp_union_mixed_beta_leg",
        r"par_reduces_cd the_red_env cdp_union_mixed_middle
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"@par_reduces_cd.beta the_red_env rfnz_nat rfnz_nat projection_binding_field projection_binding_field
  (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero))
  (@par_reduces_cd.refl the_red_env rfnz_nat)
  (@par_reduces_cd.refl the_red_env projection_binding_field)
  (@par_reduces_cd.refl the_red_env (KExpr.bvar (Nat.succ Nat.zero)))",
    ),
    DeclarationInput::Proof(
        "cdp_union_mixed_explicit_trace",
        r"cd_projection_union_star the_red_env cdp_union_mixed_source
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"@RelationStar.step KExpr
  (RelationUnion KExpr (par_reduces_cd the_red_env) (projection_parallel the_red_env))
  cdp_union_mixed_source cdp_union_mixed_middle
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))
  (@RelationUnion.right KExpr (par_reduces_cd the_red_env) (projection_parallel the_red_env)
   cdp_union_mixed_source cdp_union_mixed_middle cdp_union_mixed_projection_leg)
  (cd_projection_union_star_single_cd the_red_env cdp_union_mixed_middle
   (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) cdp_union_mixed_beta_leg)",
    ),
    DeclarationInput::Proof(
        "cdp_union_mixed_from_parallel",
        r"cd_projection_union_star the_red_env cdp_union_mixed_source
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"cdp_to_cd_projection_union_star the_red_env cdp_union_mixed_source
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) cdp_binding_beta_step",
    ),
    DeclarationInput::Proof(
        "cdp_union_mixed_to_cdp_star",
        r"par_reduces_cdp_star the_red_env cdp_union_mixed_source
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"cd_projection_union_star_to_cdp_star the_red_env cdp_union_mixed_source
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) cdp_union_mixed_explicit_trace",
    ),
    DeclarationInput::Proof(
        "cdp_union_mixed_roundtrip",
        r"cd_projection_union_star the_red_env cdp_union_mixed_source
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        r"cdp_star_to_cd_projection_union_star the_red_env cdp_union_mixed_source
  (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) cdp_union_mixed_to_cdp_star",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_cdp_union_capture",
        r"cd_projection_union_star the_red_env cdp_union_mixed_source
 (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ Nat.zero)))",
        r"cdp_union_mixed_from_parallel",
    ),
    (
        "forged_cdp_union_reverse_endpoint",
        r"par_reduces_cdp_star the_red_env cdp_union_mixed_source
 (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero))",
        r"cdp_union_mixed_to_cdp_star",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "cd_projection_union_star_single_cd",
    "cd_projection_union_star_single_projection",
    "cd_projection_union_star_trans",
    "cd_projection_union_star_context",
    "cd_projection_union_star_app",
    "cd_projection_union_star_lam",
    "cd_projection_union_star_pi",
    "cd_projection_union_star_forall_",
    "cd_projection_union_star_let_cong",
    "cd_projection_union_star_proj",
    "cdp_to_cd_projection_union_star",
    "cdp_star_to_cd_projection_union_star",
    "cd_projection_union_to_cdp",
    "cd_projection_union_star_to_cdp_star",
    "cdp_union_mixed_projection_leg",
    "cdp_union_mixed_beta_leg",
    "cdp_union_mixed_explicit_trace",
    "cdp_union_mixed_from_parallel",
    "cdp_union_mixed_to_cdp_star",
    "cdp_union_mixed_roundtrip",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "cd_projection_union_star",
    "cdp_union_mixed_source",
    "cdp_union_mixed_middle",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];
