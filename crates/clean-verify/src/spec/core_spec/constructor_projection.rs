// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructor namespace rigidity and argument transport in current reduction.
//!
//! A constructor metadata lookup excludes definition/recursor entries under the
//! same name. The actual finite reflected environment supplies this invariant;
//! collision controls refute it for two explicitly changed model environments.
//! Under that invariant, the existing parallel reduction preserves the complete
//! constructor head (including universes) and relates each selected argument.
//!
//! Thirty-six explicit checked proof records, five transparent data definitions,
//! and three Type-valued inductives retain their checked dependency order.
//! Concrete callers reduce an actual reflected Prod field and select both slots.
//! No new reduction rule, projection beta, dependent field typing, general
//! environment-admission invariant, or Rust execution correspondence is claimed.
//!
//! Prototype provenance: target-quality/constructor-registration.Vva4Pl/README.md.

use super::acceptance_in::theorem;
use crate::spec::error::SpecError;
use crate::spec::Specification;

enum DeclarationInput {
    Inductive(&'static str),
    Proof(&'static str, &'static str, &'static str),
    Data(&'static str, &'static str, &'static str),
}

const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Inductive(
        r"inductive CtorMetadataRigid (R : RedEnv) (ic : IndCtorEnv) : Type
| mk :
 (forall (n : Name) (cm : KCtorMeta),
  @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm) ->
  @Eq (OptionType KExpr) (defval_for (red_def R) n) (@OptionType.none KExpr)) ->
 (forall (n : Name) (cm : KCtorMeta),
  @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm) ->
  @Eq (OptionType RecMeta) (recmeta_for (red_rec R) n) (@OptionType.none RecMeta)) ->
 CtorMetadataRigid R ic",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_no_def",
        r"forall (R : RedEnv) (ic : IndCtorEnv) (h : CtorMetadataRigid R ic)
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)), @Eq (OptionType KExpr) (defval_for (red_def R) n) (@OptionType.none KExpr)",
        r"fun (R : RedEnv) (ic : IndCtorEnv) (h : CtorMetadataRigid R ic)
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)) => @CtorMetadataRigid.rec R ic
  (fun (_h : CtorMetadataRigid R ic) => @Eq (OptionType KExpr) (defval_for (red_def R) n) (@OptionType.none KExpr))
  (fun (hd : forall (q : Name) (qc : KCtorMeta),
    @Eq (OptionType KCtorMeta) (kctor_for ic q) (@OptionType.some KCtorMeta qc) ->
    @Eq (OptionType KExpr) (defval_for (red_def R) q) (@OptionType.none KExpr))
   (_hr : forall (q : Name) (qc : KCtorMeta),
    @Eq (OptionType KCtorMeta) (kctor_for ic q) (@OptionType.some KCtorMeta qc) ->
    @Eq (OptionType RecMeta) (recmeta_for (red_rec R) q) (@OptionType.none RecMeta)) => hd n cm found) h",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_no_rec",
        r"forall (R : RedEnv) (ic : IndCtorEnv) (h : CtorMetadataRigid R ic)
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)), @Eq (OptionType RecMeta) (recmeta_for (red_rec R) n) (@OptionType.none RecMeta)",
        r"fun (R : RedEnv) (ic : IndCtorEnv) (h : CtorMetadataRigid R ic)
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)) => @CtorMetadataRigid.rec R ic
  (fun (_h : CtorMetadataRigid R ic) => @Eq (OptionType RecMeta) (recmeta_for (red_rec R) n) (@OptionType.none RecMeta))
  (fun (_hd : forall (q : Name) (qc : KCtorMeta),
    @Eq (OptionType KCtorMeta) (kctor_for ic q) (@OptionType.some KCtorMeta qc) ->
    @Eq (OptionType KExpr) (defval_for (red_def R) q) (@OptionType.none KExpr))
   (hr : forall (q : Name) (qc : KCtorMeta),
    @Eq (OptionType KCtorMeta) (kctor_for ic q) (@OptionType.some KCtorMeta qc) ->
    @Eq (OptionType RecMeta) (recmeta_for (red_rec R) q) (@OptionType.none RecMeta)) => hr n cm found) h",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_rigid_empty",
        r"forall (R : RedEnv), CtorMetadataRigid R IndCtorEnv.empty",
        r"fun (R : RedEnv) => @CtorMetadataRigid.mk R IndCtorEnv.empty
  (fun (n : Name) (cm : KCtorMeta)
   (bad : @Eq (OptionType KCtorMeta) (kctor_for IndCtorEnv.empty n) (@OptionType.some KCtorMeta cm)) =>
   option_none_ne_some KCtorMeta cm
    (@Eq (OptionType KExpr) (defval_for (red_def R) n) (@OptionType.none KExpr)) bad)
  (fun (n : Name) (cm : KCtorMeta)
   (bad : @Eq (OptionType KCtorMeta) (kctor_for IndCtorEnv.empty n) (@OptionType.some KCtorMeta cm)) =>
   option_none_ne_some KCtorMeta cm
    (@Eq (OptionType RecMeta) (recmeta_for (red_rec R) n) (@OptionType.none RecMeta)) bad)",
    ),
    DeclarationInput::Proof(
        "kctor_for_add_ind_some_inv",
        r"forall (ic : IndCtorEnv) (added : Name) (im : KIndMeta)
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd ic added im) n) (@OptionType.some KCtorMeta cm)), @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)",
        r"fun (ic : IndCtorEnv) (added : Name) (im : KIndMeta)
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd ic added im) n) (@OptionType.some KCtorMeta cm)) => @Bool.rec
  (fun (b : Bool) =>
   @Eq (OptionType KCtorMeta)
    (@Bool.rec (fun (_ : Bool) => OptionType KCtorMeta) (kctor_for ic n) (@OptionType.none KCtorMeta) b)
    (@OptionType.some KCtorMeta cm) ->
   @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm))
  (fun (old : @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)) => old)
  (fun (bad : @Eq (OptionType KCtorMeta) (@OptionType.none KCtorMeta) (@OptionType.some KCtorMeta cm)) =>
   option_none_ne_some KCtorMeta cm
    (@Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)) bad)
  (name_eqb added n) found",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_rigid_add_ind",
        r"forall (R : RedEnv) (ic : IndCtorEnv) (added : Name) (im : KIndMeta)
 (h : CtorMetadataRigid R ic), CtorMetadataRigid R (IndCtorEnv.addInd ic added im)",
        r"fun (R : RedEnv) (ic : IndCtorEnv) (added : Name) (im : KIndMeta)
 (h : CtorMetadataRigid R ic) => @CtorMetadataRigid.mk R (IndCtorEnv.addInd ic added im)
  (fun (n : Name) (cm : KCtorMeta)
   (found : @Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd ic added im) n) (@OptionType.some KCtorMeta cm)) =>
   ctor_metadata_no_def R ic h n cm (kctor_for_add_ind_some_inv ic added im n cm found))
  (fun (n : Name) (cm : KCtorMeta)
   (found : @Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd ic added im) n) (@OptionType.some KCtorMeta cm)) =>
   ctor_metadata_no_rec R ic h n cm (kctor_for_add_ind_some_inv ic added im n cm found))",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_rigid_add_ctor",
        r"forall (R : RedEnv) (ic : IndCtorEnv) (added : Name) (added_cm : KCtorMeta)
 (h : CtorMetadataRigid R ic)
 (no_def : @Eq (OptionType KExpr) (defval_for (red_def R) added) (@OptionType.none KExpr))
 (no_rec : @Eq (OptionType RecMeta) (recmeta_for (red_rec R) added) (@OptionType.none RecMeta)), CtorMetadataRigid R (IndCtorEnv.addCtor ic added added_cm)",
        r"fun (R : RedEnv) (ic : IndCtorEnv) (added : Name) (added_cm : KCtorMeta)
 (h : CtorMetadataRigid R ic)
 (no_def : @Eq (OptionType KExpr) (defval_for (red_def R) added) (@OptionType.none KExpr))
 (no_rec : @Eq (OptionType RecMeta) (recmeta_for (red_rec R) added) (@OptionType.none RecMeta)) => @CtorMetadataRigid.mk R (IndCtorEnv.addCtor ic added added_cm)
  (fun (n : Name) (cm : KCtorMeta)
   (found : @Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addCtor ic added added_cm) n) (@OptionType.some KCtorMeta cm)) =>
   opt_pick_some_inv KCtorMeta (name_eqb added n) added_cm (kctor_for ic n) cm
    (@Eq (OptionType KExpr) (defval_for (red_def R) n) (@OptionType.none KExpr)) found
    (fun (hit : @Eq Bool (name_eqb added n) Bool.true) (_same : @Eq KCtorMeta added_cm cm) =>
     Eq.substType Name
      (fun (q : Name) => @Eq (OptionType KExpr) (defval_for (red_def R) q) (@OptionType.none KExpr))
      added n (name_eqb_eq added n hit) no_def)
    (fun (_miss : @Eq Bool (name_eqb added n) Bool.false)
     (old : @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)) =>
     ctor_metadata_no_def R ic h n cm old))
  (fun (n : Name) (cm : KCtorMeta)
   (found : @Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addCtor ic added added_cm) n) (@OptionType.some KCtorMeta cm)) =>
   opt_pick_some_inv KCtorMeta (name_eqb added n) added_cm (kctor_for ic n) cm
    (@Eq (OptionType RecMeta) (recmeta_for (red_rec R) n) (@OptionType.none RecMeta)) found
    (fun (hit : @Eq Bool (name_eqb added n) Bool.true) (_same : @Eq KCtorMeta added_cm cm) =>
     Eq.substType Name
      (fun (q : Name) => @Eq (OptionType RecMeta) (recmeta_for (red_rec R) q) (@OptionType.none RecMeta))
      added n (name_eqb_eq added n hit) no_rec)
    (fun (_miss : @Eq Bool (name_eqb added n) Bool.false)
     (old : @Eq (OptionType KCtorMeta) (kctor_for ic n) (@OptionType.some KCtorMeta cm)) =>
     ctor_metadata_no_rec R ic h n cm old))",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_delta_none",
        r"forall (R : RedEnv) (h : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e : KExpr) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), @Eq (OptionType KExpr) (delta_reduct (red_def R) e) (@OptionType.none KExpr)",
        r"fun (R : RedEnv) (h : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e : KExpr) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => delta_reduct_eq_none_of_defval_none (red_def R) e n head
  (ctor_metadata_no_def R (red_ind_ctor R) h n cm found)",
    ),
    DeclarationInput::Proof(
        "reflected_ctor_metadata_rigid",
        r"CtorMetadataRigid the_red_env (red_ind_ctor the_red_env)",
        r"ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_62 kcre_name_91 kcre_ctor_meta_91
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_61 kcre_name_37 kcre_ind_meta_37
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_60 kcre_name_63 kcre_ctor_meta_63
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_59 kcre_name_64 kcre_ctor_meta_64
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_58 kcre_name_11 kcre_ind_meta_11
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_57 kcre_name_85 kcre_ctor_meta_85
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_56 kcre_name_12 kcre_ind_meta_12
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_55 kcre_name_83 kcre_ctor_meta_83
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_54 kcre_name_14 kcre_ind_meta_14
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_53 kcre_name_71 kcre_ctor_meta_71
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_52 kcre_name_72 kcre_ctor_meta_72
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_51 kcre_name_9 kcre_ind_meta_9
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_50 kcre_name_89 kcre_ctor_meta_89
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_49 kcre_name_8 kcre_ind_meta_8
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_48 kcre_name_74 kcre_ctor_meta_74
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_47 kcre_name_75 kcre_ctor_meta_75
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_46 kcre_name_13 kcre_ind_meta_13
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_45 kcre_name_90 kcre_ctor_meta_90
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_44 kcre_name_10 kcre_ind_meta_10
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_43 kcre_name_29 kcre_ctor_meta_29
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_42 kcre_name_16 kcre_ctor_meta_16
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_41 kcre_name_6 kcre_ind_meta_6
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_40 kcre_name_25 kcre_ctor_meta_25
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_39 kcre_name_27 kcre_ctor_meta_27
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_38 kcre_name_24 kcre_ctor_meta_24
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_37 kcre_name_22 kcre_ctor_meta_22
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_36 kcre_name_26 kcre_ctor_meta_26
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_35 kcre_name_23 kcre_ctor_meta_23
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_34 kcre_name_21 kcre_ctor_meta_21
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_33 kcre_name_20 kcre_ctor_meta_20
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_32 kcre_name_28 kcre_ctor_meta_28
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_31 kcre_name_0 kcre_ind_meta_0
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_30 kcre_name_45 kcre_ctor_meta_45
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_29 kcre_name_17 kcre_ctor_meta_17
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_28 kcre_name_4 kcre_ind_meta_4
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_27 kcre_name_43 kcre_ctor_meta_43
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_26 kcre_name_41 kcre_ctor_meta_41
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_25 kcre_name_42 kcre_ctor_meta_42
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_24 kcre_name_44 kcre_ctor_meta_44
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_23 kcre_name_35 kcre_ctor_meta_35
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_22 kcre_name_3 kcre_ind_meta_3
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_21 kcre_name_70 kcre_ctor_meta_70
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_20 kcre_name_69 kcre_ctor_meta_69
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_19 kcre_name_2 kcre_ind_meta_2
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_18 kcre_name_66 kcre_ctor_meta_66
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_17 kcre_name_65 kcre_ctor_meta_65
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_16 kcre_name_40 kcre_ind_meta_40
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_15 kcre_name_67 kcre_ctor_meta_67
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_14 kcre_name_68 kcre_ctor_meta_68
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_13 kcre_name_46 kcre_ind_meta_46
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_12 kcre_name_106 kcre_ind_meta_106
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_11 kcre_name_80 kcre_ctor_meta_80
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_10 kcre_name_79 kcre_ind_meta_79
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_9 kcre_name_88 kcre_ctor_meta_88
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_8 kcre_name_87 kcre_ind_meta_87
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_7 kcre_name_82 kcre_ctor_meta_82
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_6 kcre_name_81 kcre_ind_meta_81
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_5 kcre_name_33 kcre_ctor_meta_33
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_4 kcre_name_34 kcre_ctor_meta_34
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_3 kcre_name_7 kcre_ind_meta_7
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_2 kcre_name_15 kcre_ctor_meta_15
 (ctor_metadata_rigid_add_ctor the_red_env kcre_ind_ctor_env_1 kcre_name_18 kcre_ctor_meta_18
 (ctor_metadata_rigid_add_ind the_red_env kcre_ind_ctor_env_0 kcre_name_1 kcre_ind_meta_1
 (ctor_metadata_rigid_empty the_red_env))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))))
 (@Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
 (@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta))",
    ),
    DeclarationInput::Proof(
        "reflected_prod_ctor_lookup",
        r"@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor the_red_env) kcre_prod_mk_name)
 (@OptionType.some KCtorMeta kcre_prod_ctor_meta)",
        r"@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta kcre_prod_ctor_meta)",
    ),
    DeclarationInput::Proof(
        "reflected_prod_ctor_no_def",
        r"@Eq (OptionType KExpr) (defval_for (red_def the_red_env) kcre_prod_mk_name) (@OptionType.none KExpr)",
        r"ctor_metadata_no_def the_red_env (red_ind_ctor the_red_env) reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup",
    ),
    DeclarationInput::Proof(
        "reflected_prod_ctor_no_rec",
        r"@Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) kcre_prod_mk_name) (@OptionType.none RecMeta)",
        r"ctor_metadata_no_rec the_red_env (red_ind_ctor the_red_env) reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup",
    ),
    DeclarationInput::Proof(
        "reflected_prod_value_delta_none",
        r"@Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) kcre_witness_prod_value) (@OptionType.none KExpr)",
        r"ctor_metadata_delta_none the_red_env reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup kcre_witness_prod_value
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_iota_none",
        r"forall (R : RedEnv) (h : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e : KExpr) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), @Eq (OptionType KExpr) (iota_reduct (red_rec R) e) (@OptionType.none KExpr)",
        r"fun (R : RedEnv) (h : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e : KExpr) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => Eq.subst (OptionType Name)
  (fun (hn : OptionType Name) =>
   @Eq (OptionType KExpr)
    (opt_bind Name KExpr hn (fun (rn : Name) =>
     opt_bind RecMeta KExpr (recmeta_for (red_rec R) rn) (fun (rm : RecMeta) =>
      opt_bind KExpr KExpr (list_head (list_drop (iota_major_index rm) (kapp_args e))) (fun (major : KExpr) =>
       opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cn : Name) =>
        opt_bind RecRule KExpr (recrule_for (red_rec R) rn cn) (fun (rule : RecRule) =>
         iota_contractum_at rm rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major)))))))
    (@OptionType.none KExpr))
  (@OptionType.some Name n) (kexpr_const_name (kapp_fn e))
  (Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n) head)
  (Eq.cong (OptionType RecMeta) (OptionType KExpr)
   (fun (om : OptionType RecMeta) =>
    opt_bind RecMeta KExpr om (fun (rm : RecMeta) =>
     opt_bind KExpr KExpr (list_head (list_drop (iota_major_index rm) (kapp_args e))) (fun (major : KExpr) =>
      opt_bind Name KExpr (kexpr_const_name (kapp_fn major)) (fun (cn : Name) =>
       opt_bind RecRule KExpr (recrule_for (red_rec R) n cn) (fun (rule : RecRule) =>
        iota_contractum_at rm rule (kexpr_const_levels (kapp_fn e)) (kapp_args e) (kapp_args major))))))
   (recmeta_for (red_rec R) n) (@OptionType.none RecMeta)
   (ctor_metadata_no_rec R (red_ind_ctor R) h n cm found))",
    ),
    DeclarationInput::Proof(
        "reflected_prod_value_iota_none",
        r"@Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) kcre_witness_prod_value) (@OptionType.none KExpr)",
        r"ctor_metadata_iota_none the_red_env reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup kcre_witness_prod_value
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))",
    ),
    DeclarationInput::Data(
        "ctor_rigid_def_collision_env",
        r"RedEnv",
        r"RedEnv.mk (red_rec the_red_env)
  (DefEnv.addDef (red_def the_red_env) kcre_prod_mk_name
   (KDefSig.mk kcre_prod_mk_signature (KExpr.sort Level.zero)))
  (red_ind_ctor the_red_env)",
    ),
    DeclarationInput::Data(
        "ctor_rigid_rec_collision_env",
        r"RedEnv",
        r"RedEnv.mk
  (RecEnv.addRec (red_rec the_red_env) kcre_prod_mk_name fixture_nat_rec_meta RecRules.nil)
  (red_def the_red_env) (red_ind_ctor the_red_env)",
    ),
    DeclarationInput::Proof(
        "ctor_rigid_def_collision_lookup",
        r"@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor ctor_rigid_def_collision_env) kcre_prod_mk_name)
 (@OptionType.some KCtorMeta kcre_prod_ctor_meta)",
        r"reflected_prod_ctor_lookup",
    ),
    DeclarationInput::Proof(
        "ctor_rigid_rec_collision_lookup",
        r"@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor ctor_rigid_rec_collision_env) kcre_prod_mk_name)
 (@OptionType.some KCtorMeta kcre_prod_ctor_meta)",
        r"reflected_prod_ctor_lookup",
    ),
    DeclarationInput::Proof(
        "ctor_rigid_def_collision_value",
        r"@Eq (OptionType KExpr) (defval_for (red_def ctor_rigid_def_collision_env) kcre_prod_mk_name)
 (@OptionType.some KExpr (KExpr.sort Level.zero))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort Level.zero))",
    ),
    DeclarationInput::Proof(
        "ctor_rigid_rec_collision_value",
        r"@Eq (OptionType RecMeta) (recmeta_for (red_rec ctor_rigid_rec_collision_env) kcre_prod_mk_name)
 (@OptionType.some RecMeta fixture_nat_rec_meta)",
        r"@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta fixture_nat_rec_meta)",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_def_collision_refused",
        r"forall (h : CtorMetadataRigid ctor_rigid_def_collision_env (red_ind_ctor ctor_rigid_def_collision_env)) (C : Prop), C",
        r"fun (h : CtorMetadataRigid ctor_rigid_def_collision_env (red_ind_ctor ctor_rigid_def_collision_env)) (C : Prop) => option_none_ne_some KExpr (KExpr.sort Level.zero) C
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr)
   (defval_for (red_def ctor_rigid_def_collision_env) kcre_prod_mk_name)
   (@OptionType.some KExpr (KExpr.sort Level.zero))
   (Eq.symm (OptionType KExpr)
    (defval_for (red_def ctor_rigid_def_collision_env) kcre_prod_mk_name) (@OptionType.none KExpr)
    (ctor_metadata_no_def ctor_rigid_def_collision_env (red_ind_ctor ctor_rigid_def_collision_env)
     h kcre_prod_mk_name kcre_prod_ctor_meta ctor_rigid_def_collision_lookup))
   ctor_rigid_def_collision_value)",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_rec_collision_refused",
        r"forall (h : CtorMetadataRigid ctor_rigid_rec_collision_env (red_ind_ctor ctor_rigid_rec_collision_env)) (C : Prop), C",
        r"fun (h : CtorMetadataRigid ctor_rigid_rec_collision_env (red_ind_ctor ctor_rigid_rec_collision_env)) (C : Prop) => option_none_ne_some RecMeta fixture_nat_rec_meta C
  (Eq.trans (OptionType RecMeta) (@OptionType.none RecMeta)
   (recmeta_for (red_rec ctor_rigid_rec_collision_env) kcre_prod_mk_name)
   (@OptionType.some RecMeta fixture_nat_rec_meta)
   (Eq.symm (OptionType RecMeta)
    (recmeta_for (red_rec ctor_rigid_rec_collision_env) kcre_prod_mk_name) (@OptionType.none RecMeta)
    (ctor_metadata_no_rec ctor_rigid_rec_collision_env (red_ind_ctor ctor_rigid_rec_collision_env)
     h kcre_prod_mk_name kcre_prod_ctor_meta ctor_rigid_rec_collision_lookup))
   ctor_rigid_rec_collision_value)",
    ),
    DeclarationInput::Inductive(
        r"inductive par_reduces_cd_list (R : RedEnv) : ListType KExpr -> ListType KExpr -> Type
| nil : par_reduces_cd_list R (@ListType.nil KExpr) (@ListType.nil KExpr)
| cons : forall (a b : KExpr) (xs ys : ListType KExpr),
 par_reduces_cd R a b -> par_reduces_cd_list R xs ys ->
 par_reduces_cd_list R (@ListType.cons KExpr a xs) (@ListType.cons KExpr b ys)",
    ),
    DeclarationInput::Proof(
        "par_reduces_cd_list_refl",
        r"forall (R : RedEnv) (xs : ListType KExpr), par_reduces_cd_list R xs xs",
        r"fun (R : RedEnv) (xs : ListType KExpr) => @ListType.rec KExpr (fun (zs : ListType KExpr) => par_reduces_cd_list R zs zs)
  (@par_reduces_cd_list.nil R)
  (fun (a : KExpr) (rest : ListType KExpr) (ih : par_reduces_cd_list R rest rest) =>
   @par_reduces_cd_list.cons R a a rest rest (@par_reduces_cd.refl R a) ih) xs",
    ),
    DeclarationInput::Proof(
        "par_reduces_cd_list_append",
        r"forall (R : RedEnv) (xs xs2 : ListType KExpr)
 (h : par_reduces_cd_list R xs xs2) (ys ys2 : ListType KExpr) (hy : par_reduces_cd_list R ys ys2), par_reduces_cd_list R (list_append xs ys) (list_append xs2 ys2)",
        r"fun (R : RedEnv) (xs xs2 : ListType KExpr)
 (h : par_reduces_cd_list R xs xs2) (ys ys2 : ListType KExpr) (hy : par_reduces_cd_list R ys ys2) => @par_reduces_cd_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : par_reduces_cd_list R as1 as2) =>
   par_reduces_cd_list R (list_append as1 ys) (list_append as2 ys2)) hy
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (hab : par_reduces_cd R a b)
   (_ht : par_reduces_cd_list R as1 as2)
   (ih : par_reduces_cd_list R (list_append as1 ys) (list_append as2 ys2)) =>
   @par_reduces_cd_list.cons R a b (list_append as1 ys) (list_append as2 ys2) hab ih) xs xs2 h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cd_list_tail",
        r"forall (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cd_list R xs ys), par_reduces_cd_list R (list_tail xs) (list_tail ys)",
        r"fun (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cd_list R xs ys) => @par_reduces_cd_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : par_reduces_cd_list R as1 as2) =>
   par_reduces_cd_list R (list_tail as1) (list_tail as2)) (@par_reduces_cd_list.nil R)
  (fun (a b : KExpr) (as1 as2 : ListType KExpr) (_hab : par_reduces_cd R a b)
   (ht : par_reduces_cd_list R as1 as2)
   (_ih : par_reduces_cd_list R (list_tail as1) (list_tail as2)) => ht) xs ys h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cd_list_drop",
        r"forall (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : par_reduces_cd_list R xs ys), par_reduces_cd_list R (list_drop k xs) (list_drop k ys)",
        r"fun (R : RedEnv) (k : Nat) (xs ys : ListType KExpr)
 (h : par_reduces_cd_list R xs ys) => @Nat.rec
  (fun (n : Nat) => forall (as1 as2 : ListType KExpr), par_reduces_cd_list R as1 as2 ->
   par_reduces_cd_list R (list_drop n as1) (list_drop n as2))
  (fun (as1 as2 : ListType KExpr) (ht : par_reduces_cd_list R as1 as2) => ht)
  (fun (n : Nat)
   (ih : forall (as1 as2 : ListType KExpr), par_reduces_cd_list R as1 as2 ->
    par_reduces_cd_list R (list_drop n as1) (list_drop n as2))
   (as1 as2 : ListType KExpr) (ht : par_reduces_cd_list R as1 as2) =>
   ih (list_tail as1) (list_tail as2) (par_reduces_cd_list_tail R as1 as2 ht)) k xs ys h",
    ),
    DeclarationInput::Proof(
        "par_reduces_cd_list_head_some",
        r"forall (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cd_list R xs ys) (a : KExpr) (C : Type)
 (found : @Eq (OptionType KExpr) (list_head xs) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq (OptionType KExpr) (list_head ys) (@OptionType.some KExpr b) -> par_reduces_cd R a b -> C), C",
        r"fun (R : RedEnv) (xs ys : ListType KExpr)
 (h : par_reduces_cd_list R xs ys) (a : KExpr) (C : Type)
 (found : @Eq (OptionType KExpr) (list_head xs) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq (OptionType KExpr) (list_head ys) (@OptionType.some KExpr b) -> par_reduces_cd R a b -> C) => @par_reduces_cd_list.rec R
  (fun (as1 as2 : ListType KExpr) (_h : par_reduces_cd_list R as1 as2) =>
   @Eq (OptionType KExpr) (list_head as1) (@OptionType.some KExpr a) ->
   (forall (b : KExpr), @Eq (OptionType KExpr) (list_head as2) (@OptionType.some KExpr b) -> par_reduces_cd R a b -> C) -> C)
  (fun (bad : @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr a))
   (_next : forall (b : KExpr), @Eq (OptionType KExpr) (@OptionType.none KExpr) (@OptionType.some KExpr b) -> par_reduces_cd R a b -> C) =>
   option_none_ne_some_type KExpr a C bad)
  (fun (x y : KExpr) (as1 as2 : ListType KExpr) (hxy : par_reduces_cd R x y)
   (_ht : par_reduces_cd_list R as1 as2)
   (_ih : @Eq (OptionType KExpr) (list_head as1) (@OptionType.some KExpr a) ->
    (forall (b : KExpr), @Eq (OptionType KExpr) (list_head as2) (@OptionType.some KExpr b) -> par_reduces_cd R a b -> C) -> C)
   (same : @Eq (OptionType KExpr) (@OptionType.some KExpr x) (@OptionType.some KExpr a))
   (proceed : forall (b : KExpr), @Eq (OptionType KExpr) (@OptionType.some KExpr y) (@OptionType.some KExpr b) -> par_reduces_cd R a b -> C) =>
   proceed y (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr y))
    (Eq.substType KExpr (fun (z : KExpr) => par_reduces_cd R z y) x a (option_some_inj KExpr x a same) hxy))
  xs ys h found next",
    ),
    DeclarationInput::Inductive(
        r"inductive ParCDCtorSpineView (R : RedEnv) (e e2 : KExpr) : Type
| mk : @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
 par_reduces_cd_list R (kapp_args e) (kapp_args e2) -> ParCDCtorSpineView R e e2",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_spine_preserved",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), ParCDCtorSpineView R e e2",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => @par_reduces_cd.rec R
  (fun (x y : KExpr) (_h : par_reduces_cd R x y) =>
   @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n) -> ParCDCtorSpineView R x y)
  (fun (x : KExpr) (_head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n)) => @ParCDCtorSpineView.mk R x x (@Eq.refl KExpr (kapp_fn x)) (par_reduces_cd_list_refl R (kapp_args x)))
  (fun (A A2 body body2 arg arg2 : KExpr)
 (_hA : par_reduces_cd R A A2)
 (_hbody : par_reduces_cd R body body2)
 (_harg : par_reduces_cd R arg arg2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDCtorSpineView R body body2)
 (_iharg : @Eq (OptionType Name) (kexpr_const_name (kapp_fn arg)) (@OptionType.some Name n) -> ParCDCtorSpineView R arg arg2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app (KExpr.lam A body) arg))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDCtorSpineView R (KExpr.app (KExpr.lam A body) arg) (instantiate body2 arg2)) impossible)
  (fun (f f2 a a2 : KExpr) (_hf : par_reduces_cd R f f2) (ha : par_reduces_cd R a a2)
 (ihf : @Eq (OptionType Name) (kexpr_const_name (kapp_fn f)) (@OptionType.some Name n) -> ParCDCtorSpineView R f f2)
 (_iha : @Eq (OptionType Name) (kexpr_const_name (kapp_fn a)) (@OptionType.some Name n) -> ParCDCtorSpineView R a a2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.app f a))) (@OptionType.some Name n)) =>
 @ParCDCtorSpineView.rec R f f2
  (fun (_v : ParCDCtorSpineView R f f2) => ParCDCtorSpineView R (KExpr.app f a) (KExpr.app f2 a2))
  (fun (same : @Eq KExpr (kapp_fn f2) (kapp_fn f))
   (args : par_reduces_cd_list R (kapp_args f) (kapp_args f2)) =>
   @ParCDCtorSpineView.mk R (KExpr.app f a) (KExpr.app f2 a2) same
    (par_reduces_cd_list_append R (kapp_args f) (kapp_args f2) args
     (@ListType.cons KExpr a (@ListType.nil KExpr)) (@ListType.cons KExpr a2 (@ListType.nil KExpr))
     (@par_reduces_cd_list.cons R a a2 (@ListType.nil KExpr) (@ListType.nil KExpr) ha (@par_reduces_cd_list.nil R)))) (ihf head))
  (fun (A A2 body body2 : KExpr)
 (_hA : par_reduces_cd R A A2)
 (_hbody : par_reduces_cd R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.lam A body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDCtorSpineView R (KExpr.lam A body) (KExpr.lam A2 body2)) impossible)
  (fun (A A2 body body2 : KExpr)
 (_hA : par_reduces_cd R A A2)
 (_hbody : par_reduces_cd R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.pi A body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDCtorSpineView R (KExpr.pi A body) (KExpr.pi A2 body2)) impossible)
  (fun (A A2 body body2 : KExpr)
 (_hA : par_reduces_cd R A A2)
 (_hbody : par_reduces_cd R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDCtorSpineView R A A2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.forall_ A body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDCtorSpineView R (KExpr.forall_ A body) (KExpr.forall_ A2 body2)) impossible)
  (fun (A A2 val val2 body body2 : KExpr)
 (_hA : par_reduces_cd R A A2)
 (_hval : par_reduces_cd R val val2)
 (_hbody : par_reduces_cd R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDCtorSpineView R A A2)
 (_ihval : @Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (@OptionType.some Name n) -> ParCDCtorSpineView R val val2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ A val body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDCtorSpineView R (KExpr.let_ A val body) (instantiate body2 val2)) impossible)
  (fun (x y : KExpr) (step : iota_step (red_rec R) x y) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n)) =>
 option_none_ne_some_type KExpr y (ParCDCtorSpineView R x y)
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (iota_reduct (red_rec R) x) (@OptionType.some KExpr y)
   (Eq.symm (OptionType KExpr) (iota_reduct (red_rec R) x) (@OptionType.none KExpr)
    (ctor_metadata_iota_none R rigid n cm found x head)) step))
  (fun (x y : KExpr) (step : delta_step (red_def R) x y) (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn x)) (@OptionType.some Name n)) =>
 option_none_ne_some_type KExpr y (ParCDCtorSpineView R x y)
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr) (delta_reduct (red_def R) x) (@OptionType.some KExpr y)
   (Eq.symm (OptionType KExpr) (delta_reduct (red_def R) x) (@OptionType.none KExpr)
    (ctor_metadata_delta_none R rigid n cm found x head)) step))
  (fun (A A2 val val2 body body2 : KExpr)
 (_hA : par_reduces_cd R A A2)
 (_hval : par_reduces_cd R val val2)
 (_hbody : par_reduces_cd R body body2)
 (_ihA : @Eq (OptionType Name) (kexpr_const_name (kapp_fn A)) (@OptionType.some Name n) -> ParCDCtorSpineView R A A2)
 (_ihval : @Eq (OptionType Name) (kexpr_const_name (kapp_fn val)) (@OptionType.some Name n) -> ParCDCtorSpineView R val val2)
 (_ihbody : @Eq (OptionType Name) (kexpr_const_name (kapp_fn body)) (@OptionType.some Name n) -> ParCDCtorSpineView R body body2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.let_ A val body))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDCtorSpineView R (KExpr.let_ A val body) (KExpr.let_ A2 val2 body2)) impossible)
  (fun (S : Name) (idx : Nat) (sub sub2 : KExpr) (_hs : par_reduces_cd R sub sub2)
 (_ihs : @Eq (OptionType Name) (kexpr_const_name (kapp_fn sub)) (@OptionType.some Name n) -> ParCDCtorSpineView R sub sub2)
 (impossible : @Eq (OptionType Name) (kexpr_const_name (kapp_fn (KExpr.proj S idx sub))) (@OptionType.some Name n)) =>
 option_none_ne_some_type Name n (ParCDCtorSpineView R (KExpr.proj S idx sub) (KExpr.proj S idx sub2)) impossible)
  e e2 h head",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_head_preserved",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), @Eq KExpr (kapp_fn e2) (kapp_fn e)",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => @ParCDCtorSpineView.rec R e e2
  (fun (_v : ParCDCtorSpineView R e e2) => @Eq KExpr (kapp_fn e2) (kapp_fn e))
  (fun (same : @Eq KExpr (kapp_fn e2) (kapp_fn e)) (_args : par_reduces_cd_list R (kapp_args e) (kapp_args e2)) => same)
  (ctor_metadata_spine_preserved R rigid n cm found e e2 h head)",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_spine_length",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)), @Eq Nat (list_length (kapp_args e)) (list_length (kapp_args e2))",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n)) => const_spine_length_preserved_cd R n
  (ctor_metadata_no_def R (red_ind_ctor R) rigid n cm found)
  (ctor_metadata_no_rec R (red_ind_ctor R) rigid n cm found) e e2 h head",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_selected_position",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (k : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cd R a b -> C), C",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (k : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cd R a b -> C) => @ParCDCtorSpineView.rec R e e2 (fun (_v : ParCDCtorSpineView R e e2) => C)
  (fun (same : @Eq KExpr (kapp_fn e2) (kapp_fn e)) (args : par_reduces_cd_list R (kapp_args e) (kapp_args e2)) =>
   par_reduces_cd_list_head_some R (list_drop k (kapp_args e)) (list_drop k (kapp_args e2))
    (par_reduces_cd_list_drop R k (kapp_args e) (kapp_args e2) args) a C selected
    (fun (b : KExpr)
     (found_b : @Eq (OptionType KExpr) (list_head (list_drop k (kapp_args e2))) (@OptionType.some KExpr b))
     (step : par_reduces_cd R a b) => next b same found_b step))
  (ctor_metadata_spine_preserved R rigid n cm found e e2 h head)",
    ),
    DeclarationInput::Proof(
        "ctor_metadata_selected_field",
        r"forall (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (idx : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr)
  (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cd R a b -> C), C",
        r"fun (R : RedEnv) (rigid : CtorMetadataRigid R (red_ind_ctor R))
 (n : Name) (cm : KCtorMeta)
 (found : @Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor R) n) (@OptionType.some KCtorMeta cm))
 (e e2 : KExpr) (h : par_reduces_cd R e e2)
 (head : @Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (@OptionType.some Name n))
 (idx : Nat) (a : KExpr) (C : Type)
 (selected : @Eq (OptionType KExpr)
  (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e))) (@OptionType.some KExpr a))
 (next : forall (b : KExpr), @Eq KExpr (kapp_fn e2) (kapp_fn e) ->
  @Eq (OptionType KExpr) (list_head (list_drop (Nat.add (kctor_num_params cm) idx) (kapp_args e2))) (@OptionType.some KExpr b) ->
  par_reduces_cd R a b -> C) => ctor_metadata_selected_position R rigid n cm found e e2 h head
  (Nat.add (kctor_num_params cm) idx) a C selected next",
    ),
    DeclarationInput::Data(
        "ctor_spine_prod_redex",
        r"KExpr",
        r"KExpr.app (KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)) rfnz_zero",
    ),
    DeclarationInput::Data(
        "ctor_spine_prod_prefix",
        r"KExpr",
        r"KExpr.app (KExpr.app projection_prod_ctor rfnz_nat) rfnz_nat",
    ),
    DeclarationInput::Data(
        "ctor_spine_prod_before",
        r"KExpr",
        r"KExpr.app (KExpr.app ctor_spine_prod_prefix ctor_spine_prod_redex) (KExpr.app rfnz_succ rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "ctor_spine_prod_beta",
        r"par_reduces_cd the_red_env ctor_spine_prod_redex rfnz_zero",
        r"@par_reduces_cd.beta the_red_env rfnz_nat rfnz_nat (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) rfnz_zero rfnz_zero
  (@par_reduces_cd.refl the_red_env rfnz_nat)
  (@par_reduces_cd.refl the_red_env (KExpr.bvar Nat.zero))
  (@par_reduces_cd.refl the_red_env rfnz_zero)",
    ),
    DeclarationInput::Proof(
        "ctor_spine_prod_step",
        r"par_reduces_cd the_red_env ctor_spine_prod_before kcre_witness_prod_value",
        r"@par_reduces_cd.app the_red_env
  (KExpr.app ctor_spine_prod_prefix ctor_spine_prod_redex) (KExpr.app ctor_spine_prod_prefix rfnz_zero)
  (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero)
  (@par_reduces_cd.app the_red_env ctor_spine_prod_prefix ctor_spine_prod_prefix ctor_spine_prod_redex rfnz_zero
   (@par_reduces_cd.refl the_red_env ctor_spine_prod_prefix) ctor_spine_prod_beta)
  (@par_reduces_cd.refl the_red_env (KExpr.app rfnz_succ rfnz_zero))",
    ),
    DeclarationInput::Proof(
        "ctor_spine_prod_head_preserved",
        r"@Eq KExpr (kapp_fn kcre_witness_prod_value) (kapp_fn ctor_spine_prod_before)",
        r"ctor_metadata_head_preserved the_red_env reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup
  ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))",
    ),
    DeclarationInput::Proof(
        "ctor_spine_prod_length_preserved",
        r"@Eq Nat (list_length (kapp_args ctor_spine_prod_before)) (list_length (kapp_args kcre_witness_prod_value))",
        r"ctor_metadata_spine_length the_red_env reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup
  ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))",
    ),
    DeclarationInput::Proof(
        "ctor_spine_prod_selected_zero",
        r"par_reduces_cd the_red_env ctor_spine_prod_redex rfnz_zero",
        r"ctor_metadata_selected_field the_red_env reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup
  ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))
  Nat.zero ctor_spine_prod_redex (par_reduces_cd the_red_env ctor_spine_prod_redex rfnz_zero)
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr ctor_spine_prod_redex))
  (fun (b : KExpr) (_same : @Eq KExpr (kapp_fn kcre_witness_prod_value) (kapp_fn ctor_spine_prod_before))
   (selected : @Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params kcre_prod_ctor_meta) Nat.zero) (kapp_args kcre_witness_prod_value)))
    (@OptionType.some KExpr b))
   (step : par_reduces_cd the_red_env ctor_spine_prod_redex b) =>
   Eq.substType KExpr (fun (r : KExpr) => par_reduces_cd the_red_env ctor_spine_prod_redex r) b rfnz_zero
    (Eq.symm KExpr rfnz_zero b (option_some_inj KExpr rfnz_zero b selected)) step)",
    ),
    DeclarationInput::Proof(
        "ctor_spine_prod_selected_one",
        r"par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero)",
        r"ctor_metadata_selected_field the_red_env reflected_ctor_metadata_rigid
  kcre_prod_mk_name kcre_prod_ctor_meta reflected_prod_ctor_lookup
  ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step
  (@Eq.refl (OptionType Name) (@OptionType.some Name kcre_prod_mk_name))
  (Nat.succ Nat.zero) (KExpr.app rfnz_succ rfnz_zero)
  (par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero))
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero)))
  (fun (b : KExpr) (_same : @Eq KExpr (kapp_fn kcre_witness_prod_value) (kapp_fn ctor_spine_prod_before))
   (selected : @Eq (OptionType KExpr)
    (list_head (list_drop (Nat.add (kctor_num_params kcre_prod_ctor_meta) (Nat.succ Nat.zero)) (kapp_args kcre_witness_prod_value)))
    (@OptionType.some KExpr b))
   (step : par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) b) =>
   Eq.substType KExpr (fun (r : KExpr) => par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) r)
    b (KExpr.app rfnz_succ rfnz_zero)
    (Eq.symm KExpr (KExpr.app rfnz_succ rfnz_zero) b (option_some_inj KExpr (KExpr.app rfnz_succ rfnz_zero) b selected)) step)",
    ),
];

#[cfg(test)]
const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "forged_def_collision_rigidity",
        r"CtorMetadataRigid ctor_rigid_def_collision_env (red_ind_ctor ctor_rigid_def_collision_env)",
        r"reflected_ctor_metadata_rigid",
    ),
    (
        "forged_rec_collision_rigidity",
        r"CtorMetadataRigid ctor_rigid_rec_collision_env (red_ind_ctor ctor_rigid_rec_collision_env)",
        r"reflected_ctor_metadata_rigid",
    ),
    (
        "forged_selected_constructor_target",
        r"par_reduces_cd the_red_env ctor_spine_prod_redex (KExpr.app rfnz_succ rfnz_zero)",
        r"ctor_spine_prod_selected_zero",
    ),
    (
        "forged_constructor_head_universes",
        r"@Eq KExpr (kapp_fn kcre_witness_prod_value)
  (KExpr.const kcre_prod_mk_name (@ListType.cons Level Level.zero (@ListType.nil Level)))",
        r"ctor_spine_prod_head_preserved",
    ),
];

const PROOF_ROOTS: &[&str] = &[
    "ctor_metadata_no_def",
    "ctor_metadata_no_rec",
    "ctor_metadata_rigid_empty",
    "kctor_for_add_ind_some_inv",
    "ctor_metadata_rigid_add_ind",
    "ctor_metadata_rigid_add_ctor",
    "ctor_metadata_delta_none",
    "reflected_ctor_metadata_rigid",
    "reflected_prod_ctor_lookup",
    "reflected_prod_ctor_no_def",
    "reflected_prod_ctor_no_rec",
    "reflected_prod_value_delta_none",
    "ctor_metadata_iota_none",
    "reflected_prod_value_iota_none",
    "ctor_rigid_def_collision_lookup",
    "ctor_rigid_rec_collision_lookup",
    "ctor_rigid_def_collision_value",
    "ctor_rigid_rec_collision_value",
    "ctor_metadata_def_collision_refused",
    "ctor_metadata_rec_collision_refused",
    "par_reduces_cd_list_refl",
    "par_reduces_cd_list_append",
    "par_reduces_cd_list_tail",
    "par_reduces_cd_list_drop",
    "par_reduces_cd_list_head_some",
    "ctor_metadata_spine_preserved",
    "ctor_metadata_head_preserved",
    "ctor_metadata_spine_length",
    "ctor_metadata_selected_position",
    "ctor_metadata_selected_field",
    "ctor_spine_prod_beta",
    "ctor_spine_prod_step",
    "ctor_spine_prod_head_preserved",
    "ctor_spine_prod_length_preserved",
    "ctor_spine_prod_selected_zero",
    "ctor_spine_prod_selected_one",
];

const DATA_NAMES: &[&str] = &[
    "ctor_rigid_def_collision_env",
    "ctor_rigid_rec_collision_env",
    "ctor_spine_prod_redex",
    "ctor_spine_prod_prefix",
    "ctor_spine_prod_before",
];

const INDUCTIVE_NAMES: &[&str] = &[
    "CtorMetadataRigid",
    "par_reduces_cd_list",
    "ParCDCtorSpineView",
];

impl Specification {
    /// Full bundle only, after the reflected projection metadata and spines.
    pub(super) fn add_constructor_projection(&mut self) -> Result<(), SpecError> {
        debug_assert_eq!(
            DECLARATIONS.len(),
            PROOF_ROOTS.len() + DATA_NAMES.len() + INDUCTIVE_NAMES.len()
        );
        for declaration in DECLARATIONS {
            match declaration {
                DeclarationInput::Inductive(source) => self.add_inductive(
                    source,
                    "Constructor namespace invariant or pointwise current-reduction evidence; no desired projection typing is carried.",
                )?,
                DeclarationInput::Proof(name, ty, body) => theorem(
                    self,
                    name,
                    ty,
                    body,
                    "Checked constructor rigidity/current parallel-reduction transport with finite reflected callers; not projection beta or Rust refinement.",
                )?,
                DeclarationInput::Data(name, ty, body) => self.add_recursive_def(
                    &format!("def {name} : {ty} := {body}"),
                    "Transparent model data for constructor-collision refusals or reflected Prod reduction callers.",
                )?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "constructor_projection/tests.rs"]
mod tests;
