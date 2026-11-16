// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact schematic Nat/W RHS instances for the forthcoming active iota switch.
//!
//! These are proofs about the existing model functions, not source execution.
//! Stored templates use the synthetic fixture parameter Name.anonymous; actual
//! reflected recursor parameter names must still come from RecursorVal.
//! The registered helper callers do not change fixture storage or active iota;
//! their direct operational integration remains a separate migration.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const COMMON: &[(&str, &str)] = &[
    (
        r"def recursor_schematic_params : ListType Name := @ListType.cons Name Name.anonymous (@ListType.nil Name)",
        "The singleton parameter convention of the existing synthetic Nat/W fixtures, not a reflected production Name claim.",
    ),
    (
        r"def recursor_schematic_parameter_supported : LevelParamSupport recursor_schematic_params (Level.param Name.anonymous) :=
 @LevelParamSupport.param recursor_schematic_params Name.anonymous Nat.zero
  (@Eq.refl (OptionType Nat) (@OptionType.some Nat Nat.zero))",
        "Support is proved by the actual first-match membership calculation.",
    ),
    (
        r"def recursor_schematic_self_level : Level := Level.succ (Level.param Name.anonymous)",
        "A supplied universe still containing the schematic parameter, so accidental second substitution is observable.",
    ),
];

const NAT: &[(&str, &str)] = &[
    (
        r"def nat_rec_rhs_zero_instLevels (u : Level) :
 @Eq KExpr (instLevels recursor_schematic_params (natRecRhsZero (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))) (natRecRhsZero u) :=
 @Eq.refl KExpr (natRecRhsZero u)",
        "Exact existing schematic RHS instantiated once at arbitrary u equals its existing RHS(u) builder. No closure, parameter-freedom or output-equality premise.",
    ),
    (
        r"def nat_rec_rhs_zero_param_support (ps : ListType Name) (u : Level)
 (hu : LevelParamSupport ps u) : KExprParamSupport ps (natRecRhsZero u) :=
 (@KExprParamSupport.lam ps (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.sort u)) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const zeroName (@ListType.nil Level))) (KExpr.lam (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ Nat.zero))))
  (@KExprParamSupport.pi ps (KExpr.const natName (@ListType.nil Level)) (KExpr.sort u)
  (@KExprParamSupport.const ps natName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.sort ps u hu))
  (@KExprParamSupport.lam ps (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const zeroName (@ListType.nil Level))) (KExpr.lam (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ Nat.zero)))
  (@KExprParamSupport.app ps (KExpr.bvar Nat.zero) (KExpr.const zeroName (@ListType.nil Level))
  (@KExprParamSupport.bvar ps Nat.zero)
  (@KExprParamSupport.const ps zeroName (@ListType.nil Level) (@LevelListParamSupport.nil ps)))
  (@KExprParamSupport.lam ps (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.bvar (Nat.succ Nat.zero))
  (@KExprParamSupport.pi ps (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))
  (@KExprParamSupport.const ps natName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.pi ps (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ Nat.zero)))
  (@KExprParamSupport.bvar ps Nat.zero))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
  (@KExprParamSupport.app ps (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))
  (@KExprParamSupport.const ps succName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero))))))
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero)))))",
        "Explicit support constructors over the exact current RHS definition, including every binder type and recursive-call universe. Only support of its supplied universe is assumed.",
    ),
    (
        r"def nat_rec_rhs_zero_stored_support : KExprParamSupport recursor_schematic_params (natRecRhsZero (Level.param Name.anonymous)) :=
 nat_rec_rhs_zero_param_support recursor_schematic_params (Level.param Name.anonymous) recursor_schematic_parameter_supported",
        "The once-stored schematic RHS has actual support under its singleton declaration parameters.",
    ),
    (
        r"def nat_rec_rhs_zero_stored_closed : is_closed_at (natRecRhsZero (Level.param Name.anonymous)) Nat.zero :=
 closed_at_b_sound (natRecRhsZero (Level.param Name.anonymous)) Nat.zero (@Eq.refl Bool Bool.true)",
        "Actual depth checker computation plus existing proved reflection establishes schematic de Bruijn closure; universe support is not conflated with term closedness.",
    ),
    (
        r"def nat_rec_rhs_zero_guarded (u : Level) :
 @Eq (OptionType KExpr) (recursor_rhs_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsZero (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (natRecRhsZero u)) :=
 Eq.trans (OptionType KExpr) (recursor_rhs_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsZero (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (recursor_rhs_instance (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsZero (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))))
  (@OptionType.some KExpr (natRecRhsZero u))
  (recursor_rhs_at_intro (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsZero (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)) (@Eq.refl Nat (Nat.succ Nat.zero)))
  (Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => @OptionType.some KExpr e)
    (recursor_rhs_instance (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsZero (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))) (natRecRhsZero u) (nat_rec_rhs_zero_instLevels u))",
        "Direct caller of the guarded RHS operation and the exact instance equation. The successful output is derived, not assumed.",
    ),
    (
        r"def nat_rec_rhs_zero_instance_closed (u : Level) : is_closed_at (natRecRhsZero u) Nat.zero :=
 recursor_rhs_at_preserves_closed_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsZero (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)) (natRecRhsZero u)
  (nat_rec_rhs_zero_guarded u) Nat.zero nat_rec_rhs_zero_stored_closed",
        "The guarded helper derives returned RHS closure from one stored closure proof, for every supplied universe.",
    ),
    (
        r"def nat_rec_rhs_zero_self_parameter :
 @Eq (OptionType KExpr)
  (recursor_rhs_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsZero (Level.param Name.anonymous))
    (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level)))
  (@OptionType.some KExpr (natRecRhsZero recursor_schematic_self_level)) :=
 nat_rec_rhs_zero_guarded recursor_schematic_self_level",
        "Positive actual guarded caller at succ(param anonymous), a nonclosed universe that would reveal a second substitution.",
    ),
    (
        r"def nat_rec_rhs_succ_instLevels (u : Level) :
 @Eq KExpr (instLevels recursor_schematic_params (natRecRhsSucc (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))) (natRecRhsSucc u) :=
 @Eq.refl KExpr (natRecRhsSucc u)",
        "Exact existing schematic RHS instantiated once at arbitrary u equals its existing RHS(u) builder. No closure, parameter-freedom or output-equality premise.",
    ),
    (
        r"def nat_rec_rhs_succ_param_support (ps : ListType Name) (u : Level)
 (hu : LevelParamSupport ps u) : KExprParamSupport ps (natRecRhsSucc u) :=
 (@KExprParamSupport.lam ps (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.sort u)) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const zeroName (@ListType.nil Level))) (KExpr.lam (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.lam (KExpr.const natName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))))
  (@KExprParamSupport.pi ps (KExpr.const natName (@ListType.nil Level)) (KExpr.sort u)
  (@KExprParamSupport.const ps natName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.sort ps u hu))
  (@KExprParamSupport.lam ps (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const zeroName (@ListType.nil Level))) (KExpr.lam (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.lam (KExpr.const natName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))))
  (@KExprParamSupport.app ps (KExpr.bvar Nat.zero) (KExpr.const zeroName (@ListType.nil Level))
  (@KExprParamSupport.bvar ps Nat.zero)
  (@KExprParamSupport.const ps zeroName (@ListType.nil Level) (@LevelListParamSupport.nil ps)))
  (@KExprParamSupport.lam ps (KExpr.pi (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.lam (KExpr.const natName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))
  (@KExprParamSupport.pi ps (KExpr.const natName (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))
  (@KExprParamSupport.const ps natName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.pi ps (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ Nat.zero)))
  (@KExprParamSupport.bvar ps Nat.zero))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
  (@KExprParamSupport.app ps (KExpr.const succName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))
  (@KExprParamSupport.const ps succName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero))))))
  (@KExprParamSupport.lam ps (KExpr.const natName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))
  (@KExprParamSupport.const ps natName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.app ps (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.app (KExpr.app (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero))
  (@KExprParamSupport.bvar ps Nat.zero))
  (@KExprParamSupport.app ps (KExpr.app (KExpr.app (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.app ps (KExpr.app (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar (Nat.succ Nat.zero))
  (@KExprParamSupport.app ps (KExpr.app (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
  (@KExprParamSupport.app ps (KExpr.const recName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
  (@KExprParamSupport.const ps recName (@ListType.cons Level u (@ListType.nil Level)) (@LevelListParamSupport.cons ps u (@ListType.nil Level) hu (@LevelListParamSupport.nil ps)))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ Nat.zero))))
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero)))
  (@KExprParamSupport.bvar ps Nat.zero)))))))",
        "Explicit support constructors over the exact current RHS definition, including every binder type and recursive-call universe. Only support of its supplied universe is assumed.",
    ),
    (
        r"def nat_rec_rhs_succ_stored_support : KExprParamSupport recursor_schematic_params (natRecRhsSucc (Level.param Name.anonymous)) :=
 nat_rec_rhs_succ_param_support recursor_schematic_params (Level.param Name.anonymous) recursor_schematic_parameter_supported",
        "The once-stored schematic RHS has actual support under its singleton declaration parameters.",
    ),
    (
        r"def nat_rec_rhs_succ_stored_closed : is_closed_at (natRecRhsSucc (Level.param Name.anonymous)) Nat.zero :=
 closed_at_b_sound (natRecRhsSucc (Level.param Name.anonymous)) Nat.zero (@Eq.refl Bool Bool.true)",
        "Actual depth checker computation plus existing proved reflection establishes schematic de Bruijn closure; universe support is not conflated with term closedness.",
    ),
    (
        r"def nat_rec_rhs_succ_guarded (u : Level) :
 @Eq (OptionType KExpr) (recursor_rhs_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsSucc (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (natRecRhsSucc u)) :=
 Eq.trans (OptionType KExpr) (recursor_rhs_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsSucc (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (recursor_rhs_instance (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsSucc (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))))
  (@OptionType.some KExpr (natRecRhsSucc u))
  (recursor_rhs_at_intro (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsSucc (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)) (@Eq.refl Nat (Nat.succ Nat.zero)))
  (Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => @OptionType.some KExpr e)
    (recursor_rhs_instance (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsSucc (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))) (natRecRhsSucc u) (nat_rec_rhs_succ_instLevels u))",
        "Direct caller of the guarded RHS operation and the exact instance equation. The successful output is derived, not assumed.",
    ),
    (
        r"def nat_rec_rhs_succ_instance_closed (u : Level) : is_closed_at (natRecRhsSucc u) Nat.zero :=
 recursor_rhs_at_preserves_closed_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsSucc (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)) (natRecRhsSucc u)
  (nat_rec_rhs_succ_guarded u) Nat.zero nat_rec_rhs_succ_stored_closed",
        "The guarded helper derives returned RHS closure from one stored closure proof, for every supplied universe.",
    ),
    (
        r"def nat_rec_rhs_succ_self_parameter :
 @Eq (OptionType KExpr)
  (recursor_rhs_at (KConstSig.mk recursor_schematic_params (natRecTy (Level.param Name.anonymous))) (natRecRhsSucc (Level.param Name.anonymous))
    (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level)))
  (@OptionType.some KExpr (natRecRhsSucc recursor_schematic_self_level)) :=
 nat_rec_rhs_succ_guarded recursor_schematic_self_level",
        "Positive actual guarded caller at succ(param anonymous), a nonclosed universe that would reveal a second substitution.",
    ),
];

const W: &[(&str, &str)] = &[
    (
        r"def w_rec_rhs_instLevels (u : Level) :
 @Eq KExpr (instLevels recursor_schematic_params (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))) (wRecRhs u) :=
 @Eq.refl KExpr (wRecRhs u)",
        "Exact existing schematic RHS instantiated once at arbitrary u equals its existing RHS(u) builder. No closure, parameter-freedom or output-equality premise.",
    ),
    (
        r"def w_rec_rhs_param_support (ps : ListType Name) (u : Level)
 (hu : LevelParamSupport ps u) : KExprParamSupport ps (wRecRhs u) :=
 (@KExprParamSupport.lam ps (KExpr.pi (KExpr.const wName (@ListType.nil Level)) (KExpr.sort u)) (KExpr.lam (KExpr.pi (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))) (KExpr.pi (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.const supName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.lam (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))) (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.app (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))))))
  (@KExprParamSupport.pi ps (KExpr.const wName (@ListType.nil Level)) (KExpr.sort u)
  (@KExprParamSupport.const ps wName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.sort ps u hu))
  (@KExprParamSupport.lam ps (KExpr.pi (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))) (KExpr.pi (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.const supName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.lam (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))) (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.app (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))))))
  (@KExprParamSupport.pi ps (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))) (KExpr.pi (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.const supName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))
  (@KExprParamSupport.pi ps (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))
  (@KExprParamSupport.const ps dName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.const ps wName (@ListType.nil Level) (@LevelListParamSupport.nil ps)))
  (@KExprParamSupport.pi ps (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.const supName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))))
  (@KExprParamSupport.pi ps (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))
  (@KExprParamSupport.const ps dName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ Nat.zero)))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero))
  (@KExprParamSupport.bvar ps Nat.zero))))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.app (KExpr.const supName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ Nat.zero)))
  (@KExprParamSupport.app ps (KExpr.const supName (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))
  (@KExprParamSupport.const ps supName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero))))))
  (@KExprParamSupport.lam ps (KExpr.pi (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))) (KExpr.app (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.app (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))))
  (@KExprParamSupport.pi ps (KExpr.const dName (@ListType.nil Level)) (KExpr.const wName (@ListType.nil Level))
  (@KExprParamSupport.const ps dName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.const ps wName (@ListType.nil Level) (@LevelListParamSupport.nil ps)))
  (@KExprParamSupport.app ps (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.lam (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.app (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero))
  (@KExprParamSupport.bvar ps Nat.zero))
  (@KExprParamSupport.lam ps (KExpr.const dName (@ListType.nil Level)) (KExpr.app (KExpr.app (KExpr.app (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))
  (@KExprParamSupport.const ps dName (@ListType.nil Level) (@LevelListParamSupport.nil ps))
  (@KExprParamSupport.app ps (KExpr.app (KExpr.app (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))
  (@KExprParamSupport.app ps (KExpr.app (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))
  (@KExprParamSupport.app ps (KExpr.const wRecName (@ListType.cons Level u (@ListType.nil Level))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
  (@KExprParamSupport.const ps wRecName (@ListType.cons Level u (@ListType.nil Level)) (@LevelListParamSupport.cons ps u (@ListType.nil Level) hu (@LevelListParamSupport.nil ps)))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
  (@KExprParamSupport.bvar ps (Nat.succ (Nat.succ Nat.zero))))
  (@KExprParamSupport.app ps (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)
  (@KExprParamSupport.bvar ps (Nat.succ Nat.zero))
  (@KExprParamSupport.bvar ps Nat.zero))))))))",
        "Explicit support constructors over the exact current RHS definition, including every binder type and recursive-call universe. Only support of its supplied universe is assumed.",
    ),
    (
        r"def w_rec_rhs_stored_support : KExprParamSupport recursor_schematic_params (wRecRhs (Level.param Name.anonymous)) :=
 w_rec_rhs_param_support recursor_schematic_params (Level.param Name.anonymous) recursor_schematic_parameter_supported",
        "The once-stored schematic RHS has actual support under its singleton declaration parameters.",
    ),
    (
        r"def w_rec_rhs_stored_closed : is_closed_at (wRecRhs (Level.param Name.anonymous)) Nat.zero :=
 closed_at_b_sound (wRecRhs (Level.param Name.anonymous)) Nat.zero (@Eq.refl Bool Bool.true)",
        "Actual depth checker computation plus existing proved reflection establishes schematic de Bruijn closure; universe support is not conflated with term closedness.",
    ),
    (
        r"def w_rec_rhs_guarded (u : Level) :
 @Eq (OptionType KExpr) (recursor_rhs_at (KConstSig.mk recursor_schematic_params (wRecTy (Level.param Name.anonymous))) (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (wRecRhs u)) :=
 Eq.trans (OptionType KExpr) (recursor_rhs_at (KConstSig.mk recursor_schematic_params (wRecTy (Level.param Name.anonymous))) (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (recursor_rhs_instance (KConstSig.mk recursor_schematic_params (wRecTy (Level.param Name.anonymous))) (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))))
  (@OptionType.some KExpr (wRecRhs u))
  (recursor_rhs_at_intro (KConstSig.mk recursor_schematic_params (wRecTy (Level.param Name.anonymous))) (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)) (@Eq.refl Nat (Nat.succ Nat.zero)))
  (Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => @OptionType.some KExpr e)
    (recursor_rhs_instance (KConstSig.mk recursor_schematic_params (wRecTy (Level.param Name.anonymous))) (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level))) (wRecRhs u) (w_rec_rhs_instLevels u))",
        "Direct caller of the guarded RHS operation and the exact instance equation. The successful output is derived, not assumed.",
    ),
    (
        r"def w_rec_rhs_instance_closed (u : Level) : is_closed_at (wRecRhs u) Nat.zero :=
 recursor_rhs_at_preserves_closed_at (KConstSig.mk recursor_schematic_params (wRecTy (Level.param Name.anonymous))) (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level u (@ListType.nil Level)) (wRecRhs u)
  (w_rec_rhs_guarded u) Nat.zero w_rec_rhs_stored_closed",
        "The guarded helper derives returned RHS closure from one stored closure proof, for every supplied universe.",
    ),
    (
        r"def w_rec_rhs_self_parameter :
 @Eq (OptionType KExpr)
  (recursor_rhs_at (KConstSig.mk recursor_schematic_params (wRecTy (Level.param Name.anonymous))) (wRecRhs (Level.param Name.anonymous))
    (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level)))
  (@OptionType.some KExpr (wRecRhs recursor_schematic_self_level)) :=
 w_rec_rhs_guarded recursor_schematic_self_level",
        "Positive actual guarded caller at succ(param anonymous), a nonclosed universe that would reveal a second substitution.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def recursor_rhs_motive_level (e : KExpr) : Level :=
 @KExpr.rec (fun (_e : KExpr) => Level)
  (fun (u : Level) => u) (fun (_i : Nat) => Level.zero)
  (fun (_f : KExpr) (_a : KExpr) (_ihf : Level) (_iha : Level) => Level.zero)
  (fun (_A : KExpr) (_b : KExpr) (ihA : Level) (_ihb : Level) => ihA)
  (fun (_A : KExpr) (_B : KExpr) (_ihA : Level) (ihB : Level) => ihB)
  (fun (_n : Name) (_us : ListType Level) => Level.zero)
  (fun (_A : KExpr) (_v : KExpr) (_b : KExpr) (_ihA : Level) (_ihv : Level) (_ihb : Level) => Level.zero)
  (fun (_sn : Name) (_i : Nat) (_sub : KExpr) (_ihsub : Level) => Level.zero)
  (fun (_n : Nat) => Level.zero) e",
        "A diagnostic syntactic observation only: follow lambda domains and Pi codomains to their sort. It is not an alternate reduction or typing model.",
    ),
    (
        r"def nat_rec_rhs_old_storage_double_instantiates :
 @Eq KExpr
  (instLevels recursor_schematic_params (natRecRhsZero recursor_schematic_self_level)
    (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level)))
  (natRecRhsZero (Level.succ recursor_schematic_self_level)) :=
 @Eq.refl KExpr (natRecRhsZero (Level.succ recursor_schematic_self_level))",
        "Constructive counterexample computation: the old already-instantiated storage really acquires a second successor.",
    ),
    (
        r"def nat_rec_rhs_old_storage_not_once :
 @Eq KExpr
  (instLevels recursor_schematic_params (natRecRhsZero recursor_schematic_self_level)
    (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level)))
  (natRecRhsZero recursor_schematic_self_level) -> Empty :=
 fun (bad : @Eq KExpr
  (instLevels recursor_schematic_params (natRecRhsZero recursor_schematic_self_level)
    (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level)))
  (natRecRhsZero recursor_schematic_self_level)) =>
 Eq.substType Nat
  (fun (n : Nat) => @Nat.rec (fun (_n : Nat) => Type) Nat
    (fun (_n : Nat) (_ih : Type) => Empty) n)
  Nat.zero (Nat.succ Nat.zero)
  (Eq.symm Nat (Nat.succ Nat.zero) Nat.zero
    (nat_succ_inj (Nat.succ Nat.zero) Nat.zero
      (Eq.cong KExpr Nat
        (fun (e : KExpr) => evalL (fun (_n : Name) => Nat.zero) (recursor_rhs_motive_level e))
        (instLevels recursor_schematic_params (natRecRhsZero recursor_schematic_self_level)
          (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level)))
        (natRecRhsZero recursor_schematic_self_level) bad)))
  Nat.zero",
        "The false once-instantiated result implies Empty by observing the actual motive universe and discriminating two from one. No syntactic-injectivity axiom or hoped-for output theorem.",
    ),
];

fn register(spec: &mut Specification, entries: &[(&str, &str)]) -> Result<(), SpecError> {
    for (source, description) in entries {
        spec.add_recursive_def(source, description)?;
    }
    Ok(())
}

impl Specification {
    /// Singleton parameter data/support, independent of Nat/W fixture bodies.
    pub(super) fn add_recursor_schematic_rhs_common(&mut self) -> Result<(), SpecError> {
        register(self, COMMON)
    }

    /// After Nat RHS/type definitions, guarded-RHS proofs and closed_at_b_sound.
    pub(super) fn add_nat_schematic_rhs_instances(&mut self) -> Result<(), SpecError> {
        register(self, NAT)
    }

    /// After W RHS/type definitions and the same guarded-RHS/closedness substrate.
    pub(super) fn add_w_schematic_rhs_instances(&mut self) -> Result<(), SpecError> {
        register(self, W)
    }

    /// Diagnostic control depends additionally on evalL and nat_succ_inj.
    pub(super) fn add_recursor_schematic_rhs_controls(&mut self) -> Result<(), SpecError> {
        register(self, CONTROLS)
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn schematic_rhs_instances_have_empty_actual_axiom_closures() {
        let spec = build_spec_with_stack();
        for name in [
            "recursor_schematic_parameter_supported",
            "nat_rec_rhs_zero_instLevels",
            "nat_rec_rhs_zero_param_support",
            "nat_rec_rhs_zero_stored_support",
            "nat_rec_rhs_zero_stored_closed",
            "nat_rec_rhs_zero_guarded",
            "nat_rec_rhs_zero_instance_closed",
            "nat_rec_rhs_zero_self_parameter",
            "nat_rec_rhs_succ_instLevels",
            "nat_rec_rhs_succ_param_support",
            "nat_rec_rhs_succ_stored_support",
            "nat_rec_rhs_succ_stored_closed",
            "nat_rec_rhs_succ_guarded",
            "nat_rec_rhs_succ_instance_closed",
            "nat_rec_rhs_succ_self_parameter",
            "w_rec_rhs_instLevels",
            "w_rec_rhs_param_support",
            "w_rec_rhs_stored_support",
            "w_rec_rhs_stored_closed",
            "w_rec_rhs_guarded",
            "w_rec_rhs_instance_closed",
            "w_rec_rhs_self_parameter",
            "nat_rec_rhs_old_storage_double_instantiates",
            "nat_rec_rhs_old_storage_not_once",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered schematic RHS proof");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn schematic_rhs_instances_reject_double_substitution_erasure_and_false_support() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def schematic_rhs_forged_old_once : @Eq KExpr (instLevels recursor_schematic_params (natRecRhsZero recursor_schematic_self_level) (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level))) (natRecRhsZero recursor_schematic_self_level) := @Eq.refl KExpr (natRecRhsZero recursor_schematic_self_level)",
                "def schematic_rhs_forged_w_erased : @Eq KExpr (instLevels recursor_schematic_params (wRecRhs (Level.param Name.anonymous)) (@ListType.cons Level recursor_schematic_self_level (@ListType.nil Level))) (wRecRhs Level.zero) := @Eq.refl KExpr (wRecRhs Level.zero)",
                "def schematic_rhs_forged_parameter_free : KExprParamSupport (@ListType.nil Name) (natRecRhsZero (Level.param Name.anonymous)) := nat_rec_rhs_zero_stored_support",
            ] {
                assert!(
                    spec.add_recursive_def(source, "Planted schematic RHS claim must be rejected").is_err()
                );
            }
        });
    }
}
