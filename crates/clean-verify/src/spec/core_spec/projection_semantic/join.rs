// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additive projection-aware semantic conversion: join.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive SemanticJoinCDP (R : RedEnv) (a : KExpr) (b : KExpr) : Type
| mk : forall (x y : KExpr), par_reduces_cdp_star R a x -> par_reduces_cdp_star R b y ->
 KExprUniverseEq x y -> SemanticJoinCDP R a b",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_refl",
        r"forall (R : RedEnv) (a : KExpr), SemanticJoinCDP R a a",
        r"fun (R : RedEnv) (a : KExpr) => @SemanticJoinCDP.mk R a a a a (@par_reduces_cdp_star.refl R a) (@par_reduces_cdp_star.refl R a)
  (kexprUniverseEq_refl a)",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_levels",
        r"forall (R : RedEnv) (a b : KExpr) (related : KExprUniverseEq a b), SemanticJoinCDP R a b",
        r"fun (R : RedEnv) (a b : KExpr) (related : KExprUniverseEq a b) => @SemanticJoinCDP.mk R a b a b (@par_reduces_cdp_star.refl R a) (@par_reduces_cdp_star.refl R b) related",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_raw",
        r"forall (R : RedEnv) (a b : KExpr) (raw_step : par_reduces_cdp R a b), SemanticJoinCDP R a b",
        r"fun (R : RedEnv) (a b : KExpr) (raw_step : par_reduces_cdp R a b) => @SemanticJoinCDP.mk R a b b b
  (@par_reduces_cdp_star.step R a b b raw_step (@par_reduces_cdp_star.refl R b))
  (@par_reduces_cdp_star.refl R b) (kexprUniverseEq_refl b)",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_symm",
        r"forall (R : RedEnv) (a b : KExpr) (joined : SemanticJoinCDP R a b), SemanticJoinCDP R b a",
        r"fun (R : RedEnv) (a b : KExpr) (joined : SemanticJoinCDP R a b) => @SemanticJoinCDP.rec R a b (fun (_w : SemanticJoinCDP R a b) => SemanticJoinCDP R b a)
  (fun (x y : KExpr) (ax : par_reduces_cdp_star R a x) (by_path : par_reduces_cdp_star R b y)
   (xy : KExprUniverseEq x y) =>
   @SemanticJoinCDP.mk R b a y x by_path ax (kexprUniverseEq_symm x y xy)) joined",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_trans",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R)) (a b c : KExpr)
 (ab : SemanticJoinCDP R a b) (bc : SemanticJoinCDP R b c), SemanticJoinCDP R a c",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R)) (a b c : KExpr)
 (ab : SemanticJoinCDP R a b) (bc : SemanticJoinCDP R b c) => @SemanticJoinCDP.rec R a b (fun (_ab : SemanticJoinCDP R a b) => SemanticJoinCDP R a c)
  (fun (x y : KExpr) (ax : par_reduces_cdp_star R a x)
   (by_path : par_reduces_cdp_star R b y) (xy : KExprUniverseEq x y) =>
   @SemanticJoinCDP.rec R b c (fun (_bc : SemanticJoinCDP R b c) => SemanticJoinCDP R a c)
    (fun (u v : KExpr) (bu : par_reduces_cdp_star R b u)
     (cv : par_reduces_cdp_star R c v) (uv : KExprUniverseEq u v) =>
     @RelationJoin.rec KExpr (par_reduces_cdp_star R) (par_reduces_cdp_star R) y u
      (fun (_peak : RelationJoin KExpr (par_reduces_cdp_star R) (par_reduces_cdp_star R) y u) => SemanticJoinCDP R a c)
      (fun (z : KExpr) (yz : par_reduces_cdp_star R y z) (uz : par_reduces_cdp_star R u z) =>
       par_reduces_cdp_star_universe_compat R y z yz x (kexprUniverseEq_symm x y xy)
        (SemanticJoinCDP R a c)
        (fun (x2 : KExpr) (xx2 : par_reduces_cdp_star R x x2) (zx2 : KExprUniverseEq z x2) =>
         par_reduces_cdp_star_universe_compat R u z uz v uv (SemanticJoinCDP R a c)
          (fun (v2 : KExpr) (vv2 : par_reduces_cdp_star R v v2) (zv2 : KExprUniverseEq z v2) =>
           @SemanticJoinCDP.mk R a c x2 v2
            (par_cdp_star_trans R a x x2 ax xx2) (par_cdp_star_trans R c v v2 cv vv2)
            (kexprUniverseEq_trans x2 z (kexprUniverseEq_symm z x2 zx2) v2 zv2))))
      (par_reduces_cdp_star_confluent_faithful R faithful rigid b y u by_path bu)) bc) ab",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_old_star",
        r"forall (R : RedEnv) (a b : KExpr) (path : par_reduces_cd_star R a b), par_reduces_cdp_star R a b",
        r"fun (R : RedEnv) (a b : KExpr) (path : par_reduces_cd_star R a b) => @par_reduces_cd_star.rec R
  (fun (x y : KExpr) (_p : par_reduces_cd_star R x y) => par_reduces_cdp_star R x y)
  (fun (x : KExpr) => @par_reduces_cdp_star.refl R x)
  (fun (x y z : KExpr) (first_step : par_reduces_cd R x y) (_rest : par_reduces_cd_star R y z)
   (ih : par_reduces_cdp_star R y z) =>
   @par_reduces_cdp_star.step R x y z (par_reduces_cd_to_cdp R x y first_step) ih) a b path",
    ),
    DeclarationInput::Proof(
        "semantic_join_to_cdp",
        r"forall (R : RedEnv) (a b : KExpr) (joined : SemanticJoin R a b), SemanticJoinCDP R a b",
        r"fun (R : RedEnv) (a b : KExpr) (joined : SemanticJoin R a b) => @SemanticJoin.rec R a b (fun (_old : SemanticJoin R a b) => SemanticJoinCDP R a b)
  (fun (x y : KExpr) (ax : par_reduces_cd_star R a x) (by_path : par_reduces_cd_star R b y)
   (xy : KExprUniverseEq x y) => @SemanticJoinCDP.mk R a b x y
    (semantic_join_cdp_old_star R a x ax) (semantic_join_cdp_old_star R b y by_path) xy) joined",
    ),
    DeclarationInput::Proof(
        "the_red_env_semantic_join_cdp_trans",
        r"forall (a b c : KExpr)
 (ab : SemanticJoinCDP the_red_env a b) (bc : SemanticJoinCDP the_red_env b c), SemanticJoinCDP the_red_env a c",
        r"fun (a b c : KExpr)
 (ab : SemanticJoinCDP the_red_env a b) (bc : SemanticJoinCDP the_red_env b c) => semantic_join_cdp_trans the_red_env the_red_env_faithful reflected_ctor_metadata_rigid a b c ab bc",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_projection_caller",
        r"SemanticJoinCDP the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))",
        r"semantic_join_cdp_raw the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (cdp_universe_projection_step (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_level_caller",
        r"SemanticJoinCDP the_red_env
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) (KExpr.sort (Level.succ Level.zero))",
        r"semantic_join_cdp_levels the_red_env
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))) (KExpr.sort (Level.succ Level.zero))
  (KExprUniverseEq.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)) (Level.succ Level.zero)
   (cdp_universe_nonzero_levels (Level.param Name.anonymous)))",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_composed_caller",
        r"SemanticJoinCDP the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero))",
        r"the_red_env_semantic_join_cdp_trans
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero)) semantic_join_cdp_projection_caller semantic_join_cdp_level_caller",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_reverse_caller",
        r"SemanticJoinCDP the_red_env (KExpr.sort (Level.succ Level.zero))
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))",
        r"semantic_join_cdp_symm the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort (Level.succ Level.zero)) semantic_join_cdp_composed_caller",
    ),
    DeclarationInput::Proof(
        "semantic_join_cdp_old_beta_caller",
        r"SemanticJoinCDP the_red_env ctor_spine_prod_redex rfnz_zero",
        r"semantic_join_to_cdp the_red_env ctor_spine_prod_redex rfnz_zero
  (semantic_join_raw the_red_env ctor_spine_prod_redex rfnz_zero ctor_spine_prod_beta)",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_semantic_join_cdp_wrong_leg",
        r"SemanticJoinCDP the_red_env (cdp_universe_projection (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))",
        r"@SemanticJoinCDP.mk the_red_env (cdp_universe_projection (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (@par_reduces_cdp_star.refl the_red_env (KExpr.sort (Level.succ Level.zero)))
  (@par_reduces_cdp_star.refl the_red_env (KExpr.sort (Level.succ Level.zero)))
  (kexprUniverseEq_refl (KExpr.sort (Level.succ Level.zero)))",
    ),
    (
        "forged_semantic_join_cdp_wrong_level",
        r"SemanticJoinCDP the_red_env
  (cdp_universe_projection (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
  (KExpr.sort Level.zero)",
        r"semantic_join_cdp_composed_caller",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "semantic_join_cdp_refl",
    "semantic_join_cdp_levels",
    "semantic_join_cdp_raw",
    "semantic_join_cdp_symm",
    "semantic_join_cdp_trans",
    "semantic_join_cdp_old_star",
    "semantic_join_to_cdp",
    "the_red_env_semantic_join_cdp_trans",
    "semantic_join_cdp_projection_caller",
    "semantic_join_cdp_level_caller",
    "semantic_join_cdp_composed_caller",
    "semantic_join_cdp_reverse_caller",
    "semantic_join_cdp_old_beta_caller",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["SemanticJoinCDP"];
