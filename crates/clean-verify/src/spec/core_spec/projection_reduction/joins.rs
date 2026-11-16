// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deterministic extraction and two local common-reduct constructions.

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "projection_post_whnf_deterministic",
        r"forall (R : RedEnv) (e a b : KExpr)
 (ha : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr a))
 (hb : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr b)), @Eq KExpr a b",
        r"fun (R : RedEnv) (e a b : KExpr)
 (ha : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr a))
 (hb : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr b)) => option_some_inj KExpr a b
  (Eq.trans (OptionType KExpr) (@OptionType.some KExpr a) (projection_post_whnf_reduct R e)
   (@OptionType.some KExpr b)
   (Eq.symm (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr a) ha) hb)",
    ),
    DeclarationInput::Proof(
        "par_cdp_projection_beta_beta",
        r"forall (R : RedEnv) (e a b : KExpr)
 (ha : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr a))
 (hb : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr b))
 (C : Type)
 (next : forall (v : KExpr), par_reduces_cdp R a v -> par_reduces_cdp R b v -> C), C",
        r"fun (R : RedEnv) (e a b : KExpr)
 (ha : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr a))
 (hb : @Eq (OptionType KExpr) (projection_post_whnf_reduct R e) (@OptionType.some KExpr b))
 (C : Type)
 (next : forall (v : KExpr), par_reduces_cdp R a v -> par_reduces_cdp R b v -> C) => next a (@par_reduces_cdp.refl R a)
  (Eq.substType KExpr (fun (v : KExpr) => par_reduces_cdp R b v) b a
   (projection_post_whnf_deterministic R e b a hb ha) (@par_reduces_cdp.refl R b))",
    ),
    DeclarationInput::Proof(
        "par_cdp_projection_beta_cong",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (subject subject2 : KExpr)
 (step : par_reduces_cdp R subject subject2) (a : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr), par_reduces_cdp R a b -> par_reduces_cdp R (KExpr.proj S idx subject2) b -> C), C",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (S : Name) (idx : Nat) (subject subject2 : KExpr)
 (step : par_reduces_cdp R subject subject2) (a : KExpr)
 (run : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject)) (@OptionType.some KExpr a))
 (C : Type)
 (next : forall (b : KExpr), par_reduces_cdp R a b -> par_reduces_cdp R (KExpr.proj S idx subject2) b -> C) => projection_post_whnf_transport_cdp R rigid S idx subject subject2 step a run C
  (fun (b : KExpr)
   (run2 : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S idx subject2)) (@OptionType.some KExpr b))
   (selected_step : par_reduces_cdp R a b) =>
   next b selected_step (@par_reduces_cdp.projection_beta R S idx subject2 b run2))",
    ),
    DeclarationInput::Proof(
        "par_cdp_prod_beta_projection_join",
        r"forall (C : Type)
 (next : forall (b : KExpr), par_reduces_cdp the_red_env ctor_spine_prod_redex b ->
  par_reduces_cdp the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) b -> C), C",
        r"fun (C : Type)
 (next : forall (b : KExpr), par_reduces_cdp the_red_env ctor_spine_prod_redex b ->
  par_reduces_cdp the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) b -> C) => par_cdp_projection_beta_cong the_red_env reflected_ctor_metadata_rigid kcre_prod_type_name Nat.zero
  ctor_spine_prod_before kcre_witness_prod_value
  (par_reduces_cd_to_cdp the_red_env ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step)
  ctor_spine_prod_redex projection_post_whnf_prod_before_zero C next",
    ),
];
