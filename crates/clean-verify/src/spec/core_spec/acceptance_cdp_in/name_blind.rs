// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The deployed phase-4 projection comparison, name-blind on its FIELD path.

use super::DeclarationInput;

// The deployed phase-4 projection comparison (`is_def_eq_core` ->
// `lazy_delta_proj_reduction`) never compares structure names. Its FIELD path
// -- both subjects reach constructor applications and the extracted fields are
// convertible -- is name-blind in DefEqCDPIn too, because projection beta reads
// only the index and the subject. Its SUBJECT path (e1 ~ e2 alone) is not
// carried here: DefEqCDPIn.proj keeps one name.
pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "def_eq_cdp_in_proj_field_name_blind",
        r"forall (R : RedEnv) (S1 : Name) (S2 : Name) (i : Nat) (e1 : KExpr) (t1 : KExpr) (f1 : KExpr)
 (e2 : KExpr) (t2 : KExpr) (f2 : KExpr),
 DefEqCDPIn R e1 t1 -> @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S1 i t1)) (@OptionType.some KExpr f1) ->
 DefEqCDPIn R e2 t2 -> @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S2 i t2)) (@OptionType.some KExpr f2) ->
 DefEqCDPIn R f1 f2 -> DefEqCDPIn R (KExpr.proj S1 i e1) (KExpr.proj S2 i e2)",
        r"fun (R : RedEnv) (S1 : Name) (S2 : Name) (i : Nat) (e1 : KExpr) (t1 : KExpr) (f1 : KExpr)
 (e2 : KExpr) (t2 : KExpr) (f2 : KExpr)
 (h1 : DefEqCDPIn R e1 t1) (hf1 : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S1 i t1)) (@OptionType.some KExpr f1))
 (h2 : DefEqCDPIn R e2 t2) (hf2 : @Eq (OptionType KExpr) (projection_post_whnf_reduct R (KExpr.proj S2 i t2)) (@OptionType.some KExpr f2))
 (hff : DefEqCDPIn R f1 f2) =>
@DefEqCDPIn.trans R (KExpr.proj S1 i e1) (KExpr.proj S1 i t1) (KExpr.proj S2 i e2)
  (@DefEqCDPIn.proj R S1 i e1 t1 h1)
  (@DefEqCDPIn.trans R (KExpr.proj S1 i t1) f1 (KExpr.proj S2 i e2)
    (@DefEqCDPIn.raw R (KExpr.proj S1 i t1) f1 (@par_reduces_cdp.projection_beta R S1 i t1 f1 hf1))
    (@DefEqCDPIn.trans R f1 f2 (KExpr.proj S2 i e2) hff
      (@DefEqCDPIn.symm R (KExpr.proj S2 i e2) f2
        (@DefEqCDPIn.trans R (KExpr.proj S2 i e2) (KExpr.proj S2 i t2) f2
          (@DefEqCDPIn.proj R S2 i e2 t2 h2)
          (@DefEqCDPIn.raw R (KExpr.proj S2 i t2) f2 (@par_reduces_cdp.projection_beta R S2 i t2 f2 hf2))))))",
    ),
    DeclarationInput::Data(
        r"def accepts_proj_other_name : Name := Name.str Name.anonymous (Nat.succ Nat.zero)",
    ),
    DeclarationInput::Proof(
        "accepts_proj_names_differ",
        r"@Eq Bool (name_eqb Name.anonymous accepts_proj_other_name) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "accepts_proj_other_computes",
        r"@Eq (OptionType KExpr)
  (projection_post_whnf_reduct projection_metadata_control_env (KExpr.proj accepts_proj_other_name Nat.zero accepts_proj_subject))
  (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
        r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
    ),
    DeclarationInput::Proof(
        "def_eq_cdp_in_proj_name_blind_witness",
        r"DefEqCDPIn projection_metadata_control_env accepts_proj_redex
  (KExpr.proj accepts_proj_other_name Nat.zero accepts_proj_subject)",
        r"def_eq_cdp_in_proj_field_name_blind projection_metadata_control_env Name.anonymous accepts_proj_other_name Nat.zero
  accepts_proj_subject accepts_proj_subject (KExpr.sort (Level.succ Level.zero))
  accepts_proj_subject accepts_proj_subject (KExpr.sort (Level.succ Level.zero))
  (@DefEqCDPIn.refl projection_metadata_control_env accepts_proj_subject) accepts_proj_computes
  (@DefEqCDPIn.refl projection_metadata_control_env accepts_proj_subject) accepts_proj_other_computes
  (@DefEqCDPIn.refl projection_metadata_control_env (KExpr.sort (Level.succ Level.zero)))",
    ),
];
