// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Non-seed witnesses for projections: proj-iota in a whnf premise
//! (projection beta on a constructor application), and the `proj` inference
//! arm on a variable subject -- a first field, and a DEPENDENT second field
//! whose type mentions `Proj(S, 0, e)`.

use super::DeclarationInput;

// The projection fixture reuses the one-constructor metadata environment of
// the projection-metadata stage: constructor `str anon 0`, zero parameters.
pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        r"def accepts_proj_subject : KExpr :=
KExpr.app (KExpr.const projection_metadata_control_cn (@ListType.nil Level)) (KExpr.sort (Level.succ Level.zero))",
    ),
    DeclarationInput::Data(
        r"def accepts_proj_redex : KExpr := KExpr.proj Name.anonymous Nat.zero accepts_proj_subject",
    ),
    DeclarationInput::Data(
        r"def accepts_proj_context : ListType KExpr := @ListType.cons KExpr accepts_proj_redex (@ListType.nil KExpr)",
    ),
    DeclarationInput::Proof(
        "accepts_proj_computes",
        r"@Eq (OptionType KExpr)
  (projection_post_whnf_reduct projection_metadata_control_env accepts_proj_redex)
  (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
    ),
    DeclarationInput::Proof(
        "accepts_proj_wh3_stuck",
        r"@Eq (OptionType KExpr)
  (whnf_fuel_red_wh3 projection_metadata_control_env (Nat.succ (Nat.succ Nat.zero)) accepts_proj_redex)
  (@OptionType.some KExpr accepts_proj_redex)",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr accepts_proj_redex)",
    ),
    DeclarationInput::Proof(
        "accepts_proj_trace",
        r"par_reduces_cdp_star projection_metadata_control_env accepts_proj_redex (KExpr.sort (Level.succ Level.zero))",
        r"par_cdp_to_star projection_metadata_control_env accepts_proj_redex (KExpr.sort (Level.succ Level.zero))
  (@par_reduces_cdp.projection_beta projection_metadata_control_env Name.anonymous Nat.zero
    accepts_proj_subject (KExpr.sort (Level.succ Level.zero)) accepts_proj_computes)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_in_proj_pi",
        r"forall (tenv : KDeclEnv), KernelAcceptsIn projection_metadata_control_env tenv accepts_proj_context
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
        r"fun (tenv : KDeclEnv) =>
@KernelAcceptsIn.pi projection_metadata_control_env tenv accepts_proj_context
  (KExpr.bvar Nat.zero) (KExpr.sort Level.zero) accepts_proj_redex (Level.succ Level.zero)
  (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero) (Level.succ Level.zero)
  (@KernelAcceptsIn.bvar projection_metadata_control_env tenv accepts_proj_context Nat.zero accepts_proj_redex
    (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr accepts_proj_redex)))
  accepts_proj_trace
  (@KernelAcceptsIn.sort projection_metadata_control_env tenv
    (@ListType.cons KExpr (KExpr.bvar Nat.zero) accepts_proj_context) Level.zero)
  (@par_reduces_cdp_star.refl projection_metadata_control_env (KExpr.sort (Level.succ Level.zero)))
  acceptance_imax_one_one",
    ),
    DeclarationInput::Proof(
        "accepts_proj_pi_sound",
        r"forall (tenv : KDeclEnv), TypingProjIn projection_metadata_control_env tenv accepts_proj_context
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
        r"fun (tenv : KDeclEnv) =>
kernel_accepts_in_sound projection_metadata_control_env tenv accepts_proj_context
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (kernel_accepts_in_proj_pi tenv)",
    ),
    DeclarationInput::Proof(
        "accepts_proj_seed_has_no_anonymous_inductive",
        r"@Eq (OptionType KIndMeta) (kind_for (red_ind_ctor the_red_env) Name.anonymous) (@OptionType.none KIndMeta)",
        r"@Eq.refl (OptionType KIndMeta) (@OptionType.none KIndMeta)",
    ),
    DeclarationInput::Proof(
        "accepts_proj_env_not_seed",
        r"@Eq RedEnv projection_metadata_control_env the_red_env -> Empty",
        r"fun (same : @Eq RedEnv projection_metadata_control_env the_red_env) =>
option_none_ne_some_type KIndMeta projection_metadata_control_ind Empty
  (Eq.trans (OptionType KIndMeta) (@OptionType.none KIndMeta)
    (kind_for (red_ind_ctor the_red_env) Name.anonymous)
    (@OptionType.some KIndMeta projection_metadata_control_ind)
    (Eq.symm (OptionType KIndMeta)
      (kind_for (red_ind_ctor the_red_env) Name.anonymous) (@OptionType.none KIndMeta)
      accepts_proj_seed_has_no_anonymous_inductive)
    (Eq.symm (OptionType KIndMeta) (@OptionType.some KIndMeta projection_metadata_control_ind)
      (kind_for (red_ind_ctor the_red_env) Name.anonymous)
      (Eq.cong RedEnv (OptionType KIndMeta)
        (fun (R : RedEnv) => kind_for (red_ind_ctor R) Name.anonymous)
        projection_metadata_control_env the_red_env same)))",
    ),
    // The `proj` inference arm on a VARIABLE subject whose type is the
    // one-constructor structure `const anon []` of projection_metadata_control_env
    // (constructor signature `Pi (Sort 1) (const anon [])`): field 0 has type Sort 1.
    DeclarationInput::Data(
        r"def accepts_proj_var_context : ListType KExpr := @ListType.cons KExpr projection_metadata_control_type (@ListType.nil KExpr)",
    ),
    DeclarationInput::Proof(
        "accepts_proj_var_struct",
        r"ProjStructIn projection_metadata_control_env Name.anonymous Nat.zero projection_metadata_control_type
  projection_metadata_control_ind projection_metadata_control_ctor",
        r"@ProjStructIn.mk projection_metadata_control_env Name.anonymous Nat.zero projection_metadata_control_type
  projection_metadata_control_ind projection_metadata_control_cn projection_metadata_control_ctor
  (@Eq.refl (OptionType Name) (@OptionType.some Name Name.anonymous))
  (@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta projection_metadata_control_ind))
  (@Eq.refl (ListType Name) (@ListType.cons Name projection_metadata_control_cn (@ListType.nil Name)))
  (@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta projection_metadata_control_ctor))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_in_proj_field_zero",
        r"forall (tenv : KDeclEnv), KernelAcceptsIn projection_metadata_control_env tenv accepts_proj_var_context
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero)) (KExpr.sort (Level.succ Level.zero))",
        r"fun (tenv : KDeclEnv) =>
@KernelAcceptsIn.proj projection_metadata_control_env tenv accepts_proj_var_context
  Name.anonymous Nat.zero (KExpr.bvar Nat.zero) projection_metadata_control_type projection_metadata_control_type
  projection_metadata_control_ind projection_metadata_control_ctor
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.const Name.anonymous (@ListType.nil Level)))
  (KExpr.sort (Level.succ Level.zero))
  (@KernelAcceptsIn.bvar projection_metadata_control_env tenv accepts_proj_var_context Nat.zero
    projection_metadata_control_type
    (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr projection_metadata_control_type)))
  (@par_reduces_cdp_star.refl projection_metadata_control_env projection_metadata_control_type)
  accepts_proj_var_struct
  (@ProjParamsIn.nil projection_metadata_control_env
    (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.const Name.anonymous (@ListType.nil Level))))
  (@ProjFieldIn.here projection_metadata_control_env Name.anonymous (KExpr.bvar Nat.zero) Nat.zero
    (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.const Name.anonymous (@ListType.nil Level)))
    (KExpr.sort (Level.succ Level.zero)) (KExpr.const Name.anonymous (@ListType.nil Level))
    (@par_reduces_cdp_star.refl projection_metadata_control_env
      (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.const Name.anonymous (@ListType.nil Level)))))",
    ),
    DeclarationInput::Proof(
        "accepts_proj_field_zero_sound",
        r"forall (tenv : KDeclEnv), TypingProjIn projection_metadata_control_env tenv accepts_proj_var_context
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero)) (KExpr.sort (Level.succ Level.zero))",
        r"fun (tenv : KDeclEnv) =>
kernel_accepts_in_sound projection_metadata_control_env tenv accepts_proj_var_context
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero)) (KExpr.sort (Level.succ Level.zero))
  (kernel_accepts_in_proj_field_zero tenv)",
    ),
    DeclarationInput::Proof(
        "accepts_proj_control_field_bound",
        r"@Eq Bool (nat_leb (Nat.succ (Nat.succ Nat.zero)) (kctor_num_fields projection_metadata_control_ctor)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    // A DEPENDENT second field: constructor `Pi (Sort 1) (Pi #0 (const anon []))`
    // in a two-field variant of the same structure. Field 1's type is the
    // projection of field 0, reached by the walk's `next` step.
    DeclarationInput::Data(
        r"def accepts_dep_ctor : KCtorMeta := KCtorMeta.mk
  (KConstSig.mk (@ListType.nil Name)
    (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))))
  Name.anonymous Nat.zero (Nat.succ (Nat.succ Nat.zero)) Nat.zero",
    ),
    DeclarationInput::Data(
        r"def accepts_dep_env : RedEnv := RedEnv.mk RecEnv.empty DefEnv.empty
  (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous projection_metadata_control_ind)
    projection_metadata_control_cn accepts_dep_ctor)",
    ),
    DeclarationInput::Proof(
        "accepts_dep_struct",
        r"ProjStructIn accepts_dep_env Name.anonymous (Nat.succ Nat.zero) projection_metadata_control_type
  projection_metadata_control_ind accepts_dep_ctor",
        r"@ProjStructIn.mk accepts_dep_env Name.anonymous (Nat.succ Nat.zero) projection_metadata_control_type
  projection_metadata_control_ind projection_metadata_control_cn accepts_dep_ctor
  (@Eq.refl (OptionType Name) (@OptionType.some Name Name.anonymous))
  (@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta projection_metadata_control_ind))
  (@Eq.refl (ListType Name) (@ListType.cons Name projection_metadata_control_cn (@ListType.nil Name)))
  (@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta accepts_dep_ctor))
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)",
    ),
    // The parameter walk's `cons` arm on its own: one parameter consumed through
    // the same constructor telescope, the body instantiated with it.
    DeclarationInput::Proof(
        "accepts_params_cons_witness",
        r"ProjParamsIn accepts_dep_env
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level))))
  (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr))
  (KExpr.pi (KExpr.sort Level.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))",
        r"@ProjParamsIn.cons accepts_dep_env
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level))))
  (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))
  (KExpr.sort Level.zero) (@ListType.nil KExpr)
  (KExpr.pi (KExpr.sort Level.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))
  (@par_reduces_cdp_star.refl accepts_dep_env
    (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))))
  (@ProjParamsIn.nil accepts_dep_env (KExpr.pi (KExpr.sort Level.zero) (KExpr.const Name.anonymous (@ListType.nil Level))))",
    ),
    DeclarationInput::Proof(
        "accepts_dep_field_one_walk",
        r"ProjFieldIn accepts_dep_env Name.anonymous (KExpr.bvar Nat.zero) Nat.zero (Nat.succ Nat.zero)
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level))))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))",
        r"@ProjFieldIn.next accepts_dep_env Name.anonymous (KExpr.bvar Nat.zero) Nat.zero (Nat.succ Nat.zero)
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level))))
  (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))
  (@par_reduces_cdp_star.refl accepts_dep_env
    (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))))
  (@ProjFieldIn.here accepts_dep_env Name.anonymous (KExpr.bvar Nat.zero) (Nat.succ Nat.zero)
    (KExpr.pi (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero)) (KExpr.const Name.anonymous (@ListType.nil Level)))
    (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero)) (KExpr.const Name.anonymous (@ListType.nil Level))
    (@par_reduces_cdp_star.refl accepts_dep_env
      (KExpr.pi (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero)) (KExpr.const Name.anonymous (@ListType.nil Level)))))",
    ),
    DeclarationInput::Proof(
        "kernel_accepts_in_proj_dependent_field",
        r"forall (tenv : KDeclEnv), KernelAcceptsIn accepts_dep_env tenv accepts_proj_var_context
  (KExpr.proj Name.anonymous (Nat.succ Nat.zero) (KExpr.bvar Nat.zero))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))",
        r"fun (tenv : KDeclEnv) =>
@KernelAcceptsIn.proj accepts_dep_env tenv accepts_proj_var_context
  Name.anonymous (Nat.succ Nat.zero) (KExpr.bvar Nat.zero) projection_metadata_control_type projection_metadata_control_type
  projection_metadata_control_ind accepts_dep_ctor
  (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level))))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))
  (@KernelAcceptsIn.bvar accepts_dep_env tenv accepts_proj_var_context Nat.zero
    projection_metadata_control_type
    (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr projection_metadata_control_type)))
  (@par_reduces_cdp_star.refl accepts_dep_env projection_metadata_control_type)
  accepts_dep_struct
  (@ProjParamsIn.nil accepts_dep_env
    (KExpr.pi (KExpr.sort (Level.succ Level.zero)) (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.const Name.anonymous (@ListType.nil Level)))))
  accepts_dep_field_one_walk",
    ),
    DeclarationInput::Proof(
        "accepts_proj_dependent_field_sound",
        r"forall (tenv : KDeclEnv), TypingProjIn accepts_dep_env tenv accepts_proj_var_context
  (KExpr.proj Name.anonymous (Nat.succ Nat.zero) (KExpr.bvar Nat.zero))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))",
        r"fun (tenv : KDeclEnv) =>
kernel_accepts_in_sound accepts_dep_env tenv accepts_proj_var_context
  (KExpr.proj Name.anonymous (Nat.succ Nat.zero) (KExpr.bvar Nat.zero))
  (KExpr.proj Name.anonymous Nat.zero (KExpr.bvar Nat.zero))
  (kernel_accepts_in_proj_dependent_field tenv)",
    ),
];
