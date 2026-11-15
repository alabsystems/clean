// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact composition proof tuples, with actual input derivations and explicit
//! environment assumptions. No acceptance or source-execution claim.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "cdp_confluence_cd_star_to_generic",
        r"forall (R : RedEnv) (e r : KExpr) (h : par_reduces_cd_star R e r), RelationStar KExpr (par_reduces_cd R) e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : par_reduces_cd_star R e r) => par_reduces_cd_star.rec R
 (fun (x y : KExpr) (_h : par_reduces_cd_star R x y) => RelationStar KExpr (par_reduces_cd R) x y)
 (fun (x : KExpr) => RelationStar.refl KExpr (par_reduces_cd R) x)
 (fun (x y z : KExpr) (xy : par_reduces_cd R x y) (_tail : par_reduces_cd_star R y z)
  (ih : RelationStar KExpr (par_reduces_cd R) y z) => RelationStar.step KExpr (par_reduces_cd R) x y z xy ih) e r h",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_generic_to_cd_star",
        r"forall (R : RedEnv) (e r : KExpr) (h : RelationStar KExpr (par_reduces_cd R) e r), par_reduces_cd_star R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : RelationStar KExpr (par_reduces_cd R) e r) => RelationStar.rec KExpr (par_reduces_cd R)
 (fun (x y : KExpr) (_h : RelationStar KExpr (par_reduces_cd R) x y) => par_reduces_cd_star R x y)
 (fun (x : KExpr) => par_reduces_cd_star.refl R x)
 (fun (x y z : KExpr) (xy : par_reduces_cd R x y) (_tail : RelationStar KExpr (par_reduces_cd R) y z)
  (ih : par_reduces_cd_star R y z) => par_reduces_cd_star.step R x y z xy ih) e r h",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_projection_star_to_generic",
        r"forall (R : RedEnv) (e r : KExpr) (h : projection_parallel_star R e r), RelationStar KExpr (projection_parallel R) e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : projection_parallel_star R e r) => projection_parallel_star.rec R
 (fun (x y : KExpr) (_h : projection_parallel_star R x y) => RelationStar KExpr (projection_parallel R) x y)
 (fun (x : KExpr) => RelationStar.refl KExpr (projection_parallel R) x)
 (fun (x y z : KExpr) (xy : projection_parallel R x y) (_tail : projection_parallel_star R y z)
  (ih : RelationStar KExpr (projection_parallel R) y z) => RelationStar.step KExpr (projection_parallel R) x y z xy ih) e r h",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_generic_to_projection_star",
        r"forall (R : RedEnv) (e r : KExpr) (h : RelationStar KExpr (projection_parallel R) e r), projection_parallel_star R e r",
        r"fun (R : RedEnv) (e r : KExpr) (h : RelationStar KExpr (projection_parallel R) e r) => RelationStar.rec KExpr (projection_parallel R)
 (fun (x y : KExpr) (_h : RelationStar KExpr (projection_parallel R) x y) => projection_parallel_star R x y)
 (fun (x : KExpr) => projection_parallel_star.refl R x)
 (fun (x y z : KExpr) (xy : projection_parallel R x y) (_tail : RelationStar KExpr (projection_parallel R) y z)
  (ih : projection_parallel_star R y z) => projection_parallel_star.step R x y z xy ih) e r h",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_cd_corner",
        r"forall (R : RedEnv) (i1 : RecEnvReductNotRedex (red_rec R)) (i2 : RecEnvCtorNoRecMeta (red_rec R))
(i3 : RecEnvClosed (red_rec R)) (i4 : RecEnvLiftClosed (red_rec R))
(i5 : DefEnvClosed (red_def R)) (i6 : DefEnvLiftClosed (red_def R))
(i7 : RecEnvDefEnvDisjoint R) (i8 : RecEnvCtorNoDefVal R)
 (e a b : KExpr) (ha : (RelationStar KExpr (par_reduces_cd R)) e a) (hb : (RelationStar KExpr (par_reduces_cd R)) e b), RelationJoin KExpr (RelationStar KExpr (par_reduces_cd R)) (RelationStar KExpr (par_reduces_cd R)) a b",
        r"fun (R : RedEnv) (i1 : RecEnvReductNotRedex (red_rec R)) (i2 : RecEnvCtorNoRecMeta (red_rec R))
(i3 : RecEnvClosed (red_rec R)) (i4 : RecEnvLiftClosed (red_rec R))
(i5 : DefEnvClosed (red_def R)) (i6 : DefEnvLiftClosed (red_def R))
(i7 : RecEnvDefEnvDisjoint R) (i8 : RecEnvCtorNoDefVal R)
 (e a b : KExpr) (ha : (RelationStar KExpr (par_reduces_cd R)) e a) (hb : (RelationStar KExpr (par_reduces_cd R)) e b) => par_strips_witness_cd_star.rec R a b
 (fun (_peak : par_strips_witness_cd_star R a b) => RelationJoin KExpr (RelationStar KExpr (par_reduces_cd R)) (RelationStar KExpr (par_reduces_cd R)) a b)
 (fun (meet : KExpr) (am : par_reduces_cd_star R a meet) (bm : par_reduces_cd_star R b meet) =>
  RelationJoin.mk KExpr (RelationStar KExpr (par_reduces_cd R)) (RelationStar KExpr (par_reduces_cd R)) a b meet
   (cdp_confluence_cd_star_to_generic R a meet am) (cdp_confluence_cd_star_to_generic R b meet bm))
 (par_reduces_cd_star_diamond R i1 i2 i3 i4 i5 i6 i7 i8 e a b
  (cdp_confluence_generic_to_cd_star R e a ha) (cdp_confluence_generic_to_cd_star R e b hb))",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_projection_corner",
        r"forall (R : RedEnv) (e a b : KExpr) (ha : (RelationStar KExpr (projection_parallel R)) e a) (hb : (RelationStar KExpr (projection_parallel R)) e b), RelationJoin KExpr (RelationStar KExpr (projection_parallel R)) (RelationStar KExpr (projection_parallel R)) a b",
        r"fun (R : RedEnv) (e a b : KExpr) (ha : (RelationStar KExpr (projection_parallel R)) e a) (hb : (RelationStar KExpr (projection_parallel R)) e b) => ProjectionParallelStarJoin.rec R a b
 (fun (_peak : ProjectionParallelStarJoin R a b) => RelationJoin KExpr (RelationStar KExpr (projection_parallel R)) (RelationStar KExpr (projection_parallel R)) a b)
 (fun (meet : KExpr) (am : projection_parallel_star R a meet) (bm : projection_parallel_star R b meet) =>
  RelationJoin.mk KExpr (RelationStar KExpr (projection_parallel R)) (RelationStar KExpr (projection_parallel R)) a b meet
   (cdp_confluence_projection_star_to_generic R a meet am)
   (cdp_confluence_projection_star_to_generic R b meet bm))
 (projection_parallel_star_confluent R e a b
  (cdp_confluence_generic_to_projection_star R e a ha)
  (cdp_confluence_generic_to_projection_star R e b hb))",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_mixed_corner",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R)) (e a b : KExpr) (ha : par_reduces_cd R e a) (hb : projection_parallel R e b), RelationJoin KExpr (RelationStar KExpr (projection_parallel R)) (par_reduces_cd R) a b",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R)) (e a b : KExpr) (ha : par_reduces_cd R e a) (hb : projection_parallel R e b) => CDProjectionPeak.rec R a b
 (fun (_peak : CDProjectionPeak R a b) => RelationJoin KExpr (RelationStar KExpr (projection_parallel R)) (par_reduces_cd R) a b)
 (fun (meet : KExpr) (am : projection_parallel_star R a meet) (bm : par_reduces_cd R b meet) =>
  RelationJoin.mk KExpr (RelationStar KExpr (projection_parallel R)) (par_reduces_cd R) a b meet
   (cdp_confluence_projection_star_to_generic R a meet am) bm)
 (cd_projection_strong_commute R rigid e a b ha hb)",
    ),
    DeclarationInput::Proof(
        "cd_projection_union_star_confluent",
        r"forall (R : RedEnv) (i1 : RecEnvReductNotRedex (red_rec R)) (i2 : RecEnvCtorNoRecMeta (red_rec R))
(i3 : RecEnvClosed (red_rec R)) (i4 : RecEnvLiftClosed (red_rec R))
(i5 : DefEnvClosed (red_def R)) (i6 : DefEnvLiftClosed (red_def R))
(i7 : RecEnvDefEnvDisjoint R) (i8 : RecEnvCtorNoDefVal R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (e a b : KExpr) (ha : cd_projection_union_star R e a) (hb : cd_projection_union_star R e b), RelationJoin KExpr (cd_projection_union_star R) (cd_projection_union_star R) a b",
        r"fun (R : RedEnv) (i1 : RecEnvReductNotRedex (red_rec R)) (i2 : RecEnvCtorNoRecMeta (red_rec R))
(i3 : RecEnvClosed (red_rec R)) (i4 : RecEnvLiftClosed (red_rec R))
(i5 : DefEnvClosed (red_def R)) (i6 : DefEnvLiftClosed (red_def R))
(i7 : RecEnvDefEnvDisjoint R) (i8 : RecEnvCtorNoDefVal R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (e a b : KExpr) (ha : cd_projection_union_star R e a) (hb : cd_projection_union_star R e b) => relation_union_confluent_of_strong KExpr (par_reduces_cd R) (projection_parallel R)
 (cdp_confluence_cd_corner R i1 i2 i3 i4 i5 i6 i7 i8)
 (cdp_confluence_projection_corner R)
 (cdp_confluence_mixed_corner R rigid) e a b ha hb",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_confluent",
        r"forall (R : RedEnv) (i1 : RecEnvReductNotRedex (red_rec R)) (i2 : RecEnvCtorNoRecMeta (red_rec R))
(i3 : RecEnvClosed (red_rec R)) (i4 : RecEnvLiftClosed (red_rec R))
(i5 : DefEnvClosed (red_def R)) (i6 : DefEnvLiftClosed (red_def R))
(i7 : RecEnvDefEnvDisjoint R) (i8 : RecEnvCtorNoDefVal R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (e a b : KExpr) (ha : par_reduces_cdp_star R e a) (hb : par_reduces_cdp_star R e b), RelationJoin KExpr (par_reduces_cdp_star R) (par_reduces_cdp_star R) a b",
        r"fun (R : RedEnv) (i1 : RecEnvReductNotRedex (red_rec R)) (i2 : RecEnvCtorNoRecMeta (red_rec R))
(i3 : RecEnvClosed (red_rec R)) (i4 : RecEnvLiftClosed (red_rec R))
(i5 : DefEnvClosed (red_def R)) (i6 : DefEnvLiftClosed (red_def R))
(i7 : RecEnvDefEnvDisjoint R) (i8 : RecEnvCtorNoDefVal R)
 (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (e a b : KExpr) (ha : par_reduces_cdp_star R e a) (hb : par_reduces_cdp_star R e b) => relation_join_map KExpr (cd_projection_union_star R) (cd_projection_union_star R) (par_reduces_cdp_star R) (par_reduces_cdp_star R)
 (cd_projection_union_star_to_cdp_star R) (cd_projection_union_star_to_cdp_star R) a b
 (cd_projection_union_star_confluent R i1 i2 i3 i4 i5 i6 i7 i8 rigid e a b
  (cdp_star_to_cd_projection_union_star R e a ha)
  (cdp_star_to_cd_projection_union_star R e b hb))",
    ),
    DeclarationInput::Proof(
        "par_reduces_cdp_star_confluent_faithful",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R)) (e a b : KExpr) (ha : par_reduces_cdp_star R e a) (hb : par_reduces_cdp_star R e b), RelationJoin KExpr (par_reduces_cdp_star R) (par_reduces_cdp_star R) a b",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) (rigid : CtorMetadataRigid R (red_ind_ctor R)) (e a b : KExpr) (ha : par_reduces_cdp_star R e a) (hb : par_reduces_cdp_star R e b) => par_reduces_cdp_star_confluent R
 (redenv_faithful_i1 R faithful) (redenv_faithful_i2 R faithful)
 (redenv_faithful_i3 R faithful) (redenv_faithful_i4 R faithful)
 (redenv_faithful_i5 R faithful) (redenv_faithful_i6 R faithful)
 (redenv_faithful_i7 R faithful) (redenv_faithful_i8 R faithful)
 rigid e a b ha hb",
    ),
    DeclarationInput::Proof(
        "the_red_env_cdp_star_confluent",
        r"forall (e a b : KExpr) (ha : par_reduces_cdp_star the_red_env e a) (hb : par_reduces_cdp_star the_red_env e b), RelationJoin KExpr (par_reduces_cdp_star the_red_env) (par_reduces_cdp_star the_red_env) a b",
        r"fun (e a b : KExpr) (ha : par_reduces_cdp_star the_red_env e a) (hb : par_reduces_cdp_star the_red_env e b) => par_reduces_cdp_star_confluent_faithful the_red_env the_red_env_faithful reflected_ctor_metadata_rigid e a b ha hb",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_prod_left",
        r"par_reduces_cdp_star the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before)
 (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)",
        r"par_cdp_to_star the_red_env
  (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before)
  (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)
  (par_reduces_cd_to_cdp the_red_env
   (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before)
   (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)
   cd_projection_extract_actual_left)",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_prod_right",
        r"par_reduces_cdp_star the_red_env
 (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before) ctor_spine_prod_redex",
        r"par_cdp_to_star the_red_env
  (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before) ctor_spine_prod_redex
  (projection_parallel_to_cdp the_red_env
   (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before) ctor_spine_prod_redex
   cd_projection_extract_actual_right)",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_prod_join",
        r"RelationJoin KExpr
 (par_reduces_cdp_star the_red_env) (par_reduces_cdp_star the_red_env)
 (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex",
        r"the_red_env_cdp_star_confluent
  (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before)
  (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex
  cdp_confluence_prod_left cdp_confluence_prod_right",
    ),
    DeclarationInput::Proof(
        "cdp_confluence_prod_explicit_meet",
        r"RelationJoin KExpr
 (par_reduces_cdp_star the_red_env) (par_reduces_cdp_star the_red_env)
 (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex",
        r"RelationJoin.mk KExpr (par_reduces_cdp_star the_red_env) (par_reduces_cdp_star the_red_env)
  (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) ctor_spine_prod_redex rfnz_zero
  (par_cdp_to_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)
   rfnz_zero cdp_prod_inner_step)
  (par_cdp_to_star the_red_env ctor_spine_prod_redex rfnz_zero
   (par_reduces_cd_to_cdp the_red_env ctor_spine_prod_redex rfnz_zero ctor_spine_prod_beta))",
    ),
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_cdp_confluence_without_rigidity",
        r"forall (R : RedEnv) (faithful : RedEnvFaithful R), forall (e a b : KExpr) (ha : par_reduces_cdp_star R e a) (hb : par_reduces_cdp_star R e b),
 RelationJoin KExpr (par_reduces_cdp_star R) (par_reduces_cdp_star R) a b",
        r"fun (R : RedEnv) (faithful : RedEnvFaithful R) => par_reduces_cdp_star_confluent_faithful R faithful",
    ),
    (
        "forged_cdp_confluence_wrong_field",
        r"RelationJoin KExpr
 (par_reduces_cdp_star the_red_env) (par_reduces_cdp_star the_red_env)
 (KExpr.proj kcre_prod_type_name (Nat.succ Nat.zero) kcre_witness_prod_value) ctor_spine_prod_redex",
        r"cdp_confluence_prod_join",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "cdp_confluence_cd_star_to_generic",
    "cdp_confluence_generic_to_cd_star",
    "cdp_confluence_projection_star_to_generic",
    "cdp_confluence_generic_to_projection_star",
    "cdp_confluence_cd_corner",
    "cdp_confluence_projection_corner",
    "cdp_confluence_mixed_corner",
    "cd_projection_union_star_confluent",
    "par_reduces_cdp_star_confluent",
    "par_reduces_cdp_star_confluent_faithful",
    "the_red_env_cdp_star_confluent",
    "cdp_confluence_prod_left",
    "cdp_confluence_prod_right",
    "cdp_confluence_prod_join",
    "cdp_confluence_prod_explicit_meet",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];
