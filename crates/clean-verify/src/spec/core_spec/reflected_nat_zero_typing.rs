// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual reflected Nat.zero stored/instance typing and a guarded typed caller.
//!
//! The checked slice contains 57 declarations: 56 new declarations here (19 data,
//! 37 proofs), plus the already registered nz_typing_to_semantic embedding.
//! The embedding is reused, never registered twice.
//!
//! Actual metadata/RHS/names and guarded reduction use kernel_core_red_env.
//! rfnz_tenv remains an explicit four-entry MODEL environment. The separate
//! reflected_nat_zero_source_bridge module proves its equality to the actual
//! emitted kcre_nat_tenv and transports the typing results. Keeping that bridge
//! explicit distinguishes model typing from source-data emission and fidelity.
//! Neither module proves source admission, whole iota preservation, or Rust
//! execution refinement.
//!
//! Exact checked terms: scratch/reflected-nat-zero-{rhs-typing-source,rhs-links,
//! rhs-instantiation,typed-caller}.rs, commits 10fc0b4cf and 863432e8c.
//! Guides: scratch/self-verification-reflected-nat-zero-rhs-typing-2026-09-09.md
//! and scratch/self-verification-reflected-nat-zero-typed-caller-2026-09-09.md.
//! Proof records below only desugar original binders into explicit forall/fun;
//! no production parser reconstructs proofs and no status is changed afterward.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

const DECLARATIONS: &[(&str, &str)] = &[
    (r"def rfnz_nat : KExpr := KExpr.const literal_builtin_nat_name (@ListType.nil Level)", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_zero : KExpr := KExpr.const fixture_nat_zero_name (@ListType.nil Level)", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_succ : KExpr := KExpr.const fixture_nat_succ_name (@ListType.nil Level)", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_rec_signature : KConstSig := recmeta_signature fixture_nat_rec_meta", "Read the actual source-reflected Nat.rec signature from the current metadata; stored data is not an admission theorem."),
    (r"def rfnz_parameter : Name := @ListType.rec Name (fun (_ : ListType Name) => Name) Name.anonymous (fun (n : Name) (_ns : ListType Name) (_ih : Name) => n) (kconst_params rfnz_rec_signature)", "Read the first actual stored ordered universe parameter; its singleton shape is checked separately."),
    (r"def rfnz_motive_type (u : Level) : KExpr := KExpr.pi rfnz_nat (KExpr.sort u)", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_sarm : KExpr := KExpr.pi rfnz_nat (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))))", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_rec_type (u : Level) : KExpr := KExpr.pi (rfnz_motive_type u) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.pi rfnz_nat (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_rhs (u : Level) : KExpr := KExpr.lam (rfnz_motive_type u) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.lam rfnz_sarm (KExpr.bvar (Nat.succ Nat.zero))))", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_parameter_list : @Eq (ListType Name) (kconst_params rfnz_rec_signature) (@ListType.cons Name rfnz_parameter (@ListType.nil Name)) := @Eq.refl (ListType Name) (@ListType.cons Name rfnz_parameter (@ListType.nil Name))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_signature_shape : @Eq KConstSig rfnz_rec_signature (KConstSig.mk (@ListType.cons Name rfnz_parameter (@ListType.nil Name)) (rfnz_rec_type (Level.param rfnz_parameter))) := @Eq.refl KConstSig rfnz_rec_signature", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_tenv (nm : Name) : OptionType KConstSig :=
 @Bool.rec (fun (_ : Bool) => OptionType KConstSig)
  (@Bool.rec (fun (_ : Bool) => OptionType KConstSig)
   (@Bool.rec (fun (_ : Bool) => OptionType KConstSig)
    (@Bool.rec (fun (_ : Bool) => OptionType KConstSig)
     (@OptionType.none KConstSig) (@OptionType.some KConstSig rfnz_rec_signature)
     (name_eqb nm fixture_nat_rec_name))
    (@OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) (KExpr.pi rfnz_nat rfnz_nat)))
    (name_eqb nm fixture_nat_succ_name))
   (@OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) rfnz_nat))
   (name_eqb nm fixture_nat_zero_name))
  (@OptionType.some KConstSig (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.succ Level.zero))))
  (name_eqb nm literal_builtin_nat_name)", "Explicit four-entry actual-name MODEL typing environment; source-derived emission/fidelity agreement is handled by the separate checked source bridge."),
    (r"def rfnz_nat_lookup : @Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv literal_builtin_nat_name (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_zero_lookup : @Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv fixture_nat_zero_name (@ListType.nil Level)) (@OptionType.some KExpr rfnz_nat) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat)", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_succ_lookup : @Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv fixture_nat_succ_name (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.pi rfnz_nat rfnz_nat)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi rfnz_nat rfnz_nat))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_rec_lookup (u : Level) : @Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level))) (@OptionType.some KExpr (rfnz_rec_type u)) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_rec_type u))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_rule_type (u : Level) : KExpr := (KExpr.pi (rfnz_motive_type u) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero))))", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_nat_typed (G : ListType KExpr) : TypingCtx rfnz_tenv G rfnz_nat (KExpr.sort (Level.succ Level.zero)) := @TypingCtx.const rfnz_tenv G literal_builtin_nat_name (@ListType.nil Level) (KExpr.sort (Level.succ Level.zero)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_zero_typed (G : ListType KExpr) : TypingCtx rfnz_tenv G rfnz_zero rfnz_nat := @TypingCtx.const rfnz_tenv G fixture_nat_zero_name (@ListType.nil Level) rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_succ_typed (G : ListType KExpr) : TypingCtx rfnz_tenv G rfnz_succ (KExpr.pi rfnz_nat rfnz_nat) := @TypingCtx.const rfnz_tenv G fixture_nat_succ_name (@ListType.nil Level) (KExpr.pi rfnz_nat rfnz_nat) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi rfnz_nat rfnz_nat)))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_motive_typed (u : Level) (G : ListType KExpr) : TypingCtx rfnz_tenv G (rfnz_motive_type u) (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ u))) := @TypingCtx.pi rfnz_tenv G rfnz_nat (KExpr.sort u) (Level.succ Level.zero) (Level.succ u) (rfnz_nat_typed G) (@TypingCtx.sort rfnz_tenv (@ListType.cons KExpr rfnz_nat G) u)", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_zero_domain_typed (u : Level) : TypingCtx rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.sort u) := (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) (KExpr.bvar Nat.zero) rfnz_zero rfnz_nat (KExpr.sort u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) Nat.zero (rfnz_motive_type u) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_motive_type u)))) (rfnz_zero_typed (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_sarm_typed (u : Level) : TypingCtx rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))) rfnz_sarm (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.imax u u))) := @TypingCtx.pi rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))) rfnz_nat (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (Level.succ Level.zero) (Level.imax u u) (rfnz_nat_typed (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (@TypingCtx.pi rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) u u (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero) rfnz_nat (KExpr.sort u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (Nat.succ (Nat.succ Nat.zero)) (rfnz_motive_type u) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_motive_type u)))) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) Nat.zero rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat)))) (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))) rfnz_nat (KExpr.sort u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (rfnz_motive_type u) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_motive_type u)))) (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)) rfnz_nat rfnz_nat (rfnz_succ_typed (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))))) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) (Nat.succ Nat.zero) rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat))))))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_rhs_typed (u : Level) : TypingCtx rfnz_tenv (@ListType.nil KExpr) (rfnz_rhs u) (rfnz_rule_type u) := (@TypingCtx.lam rfnz_tenv (@ListType.nil KExpr) (rfnz_motive_type u) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.lam rfnz_sarm (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero))) (Level.imax (Level.succ Level.zero) (Level.succ u)) (rfnz_motive_typed u (@ListType.nil KExpr)) (@TypingCtx.lam rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.lam rfnz_sarm (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) u (rfnz_zero_domain_typed u) (@TypingCtx.lam rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))) rfnz_sarm (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero) (Level.imax (Level.succ Level.zero) (Level.imax u u)) (rfnz_sarm_typed u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_sarm (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (Nat.succ Nat.zero) (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero)))))))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_stored_rhs_shape : @Eq KExpr kcre_witness_nat_zero_rhs (rfnz_rhs (Level.param rfnz_parameter)) := @Eq.refl KExpr kcre_witness_nat_zero_rhs", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_stored_rhs_typed : TypingCtx rfnz_tenv (@ListType.nil KExpr) kcre_witness_nat_zero_rhs (rfnz_rule_type (Level.param rfnz_parameter)) := rfnz_rhs_typed (Level.param rfnz_parameter)", "Direct typing of the exact source-reflected stored Nat.zero RHS in the explicit four-entry model typing environment, with no typing-result oracle."),
    (r"def rfnz_actual_metadata : @Eq (OptionType RecMeta) (recmeta_for (red_rec kernel_core_red_env) fixture_nat_rec_name) (@OptionType.some RecMeta fixture_nat_rec_meta) := @Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta fixture_nat_rec_meta)", "Computed metadata lookup in the actual reflected reduction environment, not an assumed environment law."),
    (r"def rfnz_actual_zero_rule : @Eq (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name) (@OptionType.some RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)) := @Eq.refl (OptionType RecRule) (@OptionType.some RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs))", "Computed stored zero-rule lookup in the actual reflected reduction environment."),
    (r"def rfnz_lookup_rhs_typed (rule : RecRule)
 (h : @Eq (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name) (@OptionType.some RecRule rule)) :
 TypingCtx rfnz_tenv (@ListType.nil KExpr) (recrule_rhs rule)
  (rfnz_rule_type (Level.param rfnz_parameter)) :=
 @Eq.rec RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  (fun (r : RecRule) (_eq : @Eq RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs) r) =>
   TypingCtx rfnz_tenv (@ListType.nil KExpr) (recrule_rhs r)
    (rfnz_rule_type (Level.param rfnz_parameter)))
  rfnz_stored_rhs_typed rule
  (Eq.symm RecRule rule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
   (option_some_inj RecRule rule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
    (Eq.trans (OptionType RecRule) (@OptionType.some RecRule rule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
     (@OptionType.some RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs))
     (Eq.symm (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name) (@OptionType.some RecRule rule) h)
     rfnz_actual_zero_rule)))", "The actual stored-rule lookup selects the directly typed RHS; equality transport does not assume RHS typing."),
    (r"def rfnz_rec_signature_supported : KExprParamSupport (kconst_params rfnz_rec_signature) (kconst_type rfnz_rec_signature) := (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.sort (Level.param rfnz_parameter))) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const fixture_nat_zero_name (@ListType.nil Level))) (KExpr.pi (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.sort (Level.param rfnz_parameter)) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.sort (kconst_params rfnz_rec_signature) (Level.param rfnz_parameter) (@LevelParamSupport.param (kconst_params rfnz_rec_signature) rfnz_parameter Nat.zero (@Eq.refl (OptionType Nat) (@OptionType.some Nat Nat.zero))))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const fixture_nat_zero_name (@ListType.nil Level))) (KExpr.pi (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar Nat.zero) (KExpr.const fixture_nat_zero_name (@ListType.nil Level)) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) Nat.zero) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) fixture_nat_zero_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature)))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))))) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ (Nat.succ Nat.zero))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) Nat.zero)) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) fixture_nat_succ_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ Nat.zero)))))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) Nat.zero))))))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_tenv_extend_supported (key : Name) (sig : KConstSig) (rest : KDeclEnv)
 (hs : KExprParamSupport (kconst_params sig) (kconst_type sig))
 (hr : KDeclEnvTypeParamSupported rest) :
 KDeclEnvTypeParamSupported (fun (n : Name) => opt_pick KConstSig (name_eqb n key) sig (rest n)) :=
 fun (query : Name) (selected : KConstSig)
 (found : @Eq (OptionType KConstSig) (opt_pick KConstSig (name_eqb query key) sig (rest query)) (@OptionType.some KConstSig selected)) =>
 opt_pick_some_inv KConstSig (name_eqb query key) sig (rest query) selected
  (KExprParamSupport (kconst_params selected) (kconst_type selected)) found
  (fun (_matched : @Eq Bool (name_eqb query key) Bool.true) (same : @Eq KConstSig sig selected) =>
   Eq.subst KConstSig (fun (entry : KConstSig) => KExprParamSupport (kconst_params entry) (kconst_type entry)) sig selected same hs)
  (fun (_missed : @Eq Bool (name_eqb query key) Bool.false)
   (tail : @Eq (OptionType KConstSig) (rest query) (@OptionType.some KConstSig selected)) =>
   hr query selected tail)", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_tenv_supported : KDeclEnvTypeParamSupported rfnz_tenv :=
 rfnz_tenv_extend_supported literal_builtin_nat_name (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.succ Level.zero))) (fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_zero_name) (KConstSig.mk (@ListType.nil Name) rfnz_nat) ((fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_succ_name) (KConstSig.mk (@ListType.nil Name) (KExpr.pi rfnz_nat rfnz_nat)) ((fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_rec_name) rfnz_rec_signature (@OptionType.none KConstSig)) n)) n))
  (@KExprParamSupport.sort (@ListType.nil Name) (Level.succ Level.zero) (@LevelParamSupport.succ (@ListType.nil Name) Level.zero (@LevelParamSupport.zero (@ListType.nil Name))))
  (rfnz_tenv_extend_supported fixture_nat_zero_name (KConstSig.mk (@ListType.nil Name) rfnz_nat) (fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_succ_name) (KConstSig.mk (@ListType.nil Name) (KExpr.pi rfnz_nat rfnz_nat)) ((fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_rec_name) rfnz_rec_signature (@OptionType.none KConstSig)) n))
   (@KExprParamSupport.const (@ListType.nil Name) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (@ListType.nil Name)))
   (rfnz_tenv_extend_supported fixture_nat_succ_name (KConstSig.mk (@ListType.nil Name) (KExpr.pi rfnz_nat rfnz_nat)) (fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_rec_name) rfnz_rec_signature (@OptionType.none KConstSig))
    (@KExprParamSupport.pi (@ListType.nil Name) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (@KExprParamSupport.const (@ListType.nil Name) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (@ListType.nil Name))) (@KExprParamSupport.const (@ListType.nil Name) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (@ListType.nil Name))))
    (kdecl_env_type_param_supported_singleton fixture_nat_rec_name rfnz_rec_signature rfnz_rec_signature_supported)))", "Derive schematic type parameter support from the four finite stored signatures, not an environment-wide assumption."),
    (r"def rfnz_rhs_instance_shape (u : Level) : @Eq KExpr
 (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))
 (rfnz_rhs u) := @Eq.refl KExpr (rfnz_rhs u)", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_rule_type_instance_shape (u : Level) : @Eq KExpr
 (instLevels (kconst_params rfnz_rec_signature) (rfnz_rule_type (Level.param rfnz_parameter)) (@ListType.cons Level u (@ListType.nil Level)))
 (rfnz_rule_type u) := @Eq.refl KExpr (rfnz_rule_type u)", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_lookup_instance_typed (rule : RecRule)
 (found : @Eq (OptionType RecRule)
  (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
  (@OptionType.some RecRule rule)) (u : Level) :
 TypingCtx rfnz_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance rfnz_rec_signature (recrule_rhs rule) (@ListType.cons Level u (@ListType.nil Level)))
  (rfnz_rule_type u) :=
 typingctx_instLevels rfnz_tenv rfnz_tenv_supported
  (kconst_params rfnz_rec_signature) (@ListType.cons Level u (@ListType.nil Level))
  (@ListType.nil KExpr) (recrule_rhs rule) (rfnz_rule_type (Level.param rfnz_parameter))
  (rfnz_lookup_rhs_typed rule found)", "Consume actual looked-up stored-RHS typing via the existing universe-substitution theorem, with finite signature support discharged."),
    (r"def rfnz_actual_instance_typed (u : Level) :
 TypingCtx rfnz_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))
  (rfnz_rule_type u) :=
 rfnz_lookup_instance_typed (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  rfnz_actual_zero_rule u", "Typing of the actual once-instantiated zero RHS at arbitrary raw universe, derived from actual stored lookup."),
    (r"def rfnz_self_parameter_instance_typed :
 TypingCtx rfnz_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs
   (@ListType.cons Level (Level.succ (Level.param rfnz_parameter)) (@ListType.nil Level)))
  (rfnz_rule_type (Level.succ (Level.param rfnz_parameter))) :=
 rfnz_actual_instance_typed (Level.succ (Level.param rfnz_parameter))", "A nonclosed supplied universe exercises the actual raw instance proof without a closed-level restriction."),
    (r"def rfnz_rec (u : Level) : KExpr := KExpr.const fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level))", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_rec_typed (u : Level) : TypingCtx rfnz_tenv (@ListType.nil KExpr) (rfnz_rec u) (rfnz_rec_type u) :=
 @TypingCtx.const rfnz_tenv (@ListType.nil KExpr) fixture_nat_rec_name
  (@ListType.cons Level u (@ListType.nil Level)) (rfnz_rec_type u) (rfnz_rec_lookup u)", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_rec_app (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) (major : KExpr) : KExpr :=
 KExpr.app (KExpr.app (KExpr.app (KExpr.app (rfnz_rec u) m) z) s) major", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_env : RedEnv := kernel_core_red_env", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_motive : KExpr := (KExpr.lam rfnz_nat rfnz_nat)", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_minor : KExpr := (KExpr.lam rfnz_nat (KExpr.lam rfnz_nat (KExpr.app rfnz_succ (KExpr.bvar Nat.zero))))", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_minor_type : KExpr := (KExpr.pi rfnz_nat (KExpr.pi (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) (KExpr.app rfnz_motive (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))))", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_motive_core_typed : TypingCtx rfnz_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) :=
 @TypingCtx.lam rfnz_tenv (@ListType.nil KExpr) rfnz_nat rfnz_nat (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero)
 (rfnz_nat_typed (@ListType.nil KExpr)) (rfnz_nat_typed (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr)))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_minor_core_typed : TypingCtx rfnz_tenv (@ListType.nil KExpr) rfnz_minor (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat)) :=
 @TypingCtx.lam rfnz_tenv (@ListType.nil KExpr) rfnz_nat (KExpr.lam rfnz_nat (KExpr.app rfnz_succ (KExpr.bvar Nat.zero))) (KExpr.pi rfnz_nat rfnz_nat) (Level.succ Level.zero)
 (rfnz_nat_typed (@ListType.nil KExpr))
 (@TypingCtx.lam rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr)) rfnz_nat (KExpr.app rfnz_succ (KExpr.bvar Nat.zero)) rfnz_nat (Level.succ Level.zero)
  (rfnz_nat_typed (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr)))
  (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr))) rfnz_succ (KExpr.bvar Nat.zero) rfnz_nat rfnz_nat
   (rfnz_succ_typed (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr))))
   (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr))) Nat.zero rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat)))))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_motive_beta (x : KExpr) : DefEqIn rfnz_env (KExpr.app rfnz_motive x) rfnz_nat :=
 def_eq_in_beta rfnz_env rfnz_nat rfnz_nat x", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_minor_type_conversion : DefEqIn rfnz_env (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat)) rfnz_minor_type :=
 @DefEqIn.pi rfnz_env rfnz_nat rfnz_nat (KExpr.pi rfnz_nat rfnz_nat) (KExpr.pi (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) (KExpr.app rfnz_motive (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))))
  (@DefEqIn.refl rfnz_env rfnz_nat)
  (@DefEqIn.pi rfnz_env rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) rfnz_nat (KExpr.app rfnz_motive (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))
   (@DefEqIn.symm rfnz_env (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) rfnz_nat (rfnz_motive_beta (KExpr.bvar Nat.zero)))
   (@DefEqIn.symm rfnz_env (KExpr.app rfnz_motive (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) rfnz_nat (rfnz_motive_beta (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_motive_argument_typed : TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) := (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) rfnz_motive_core_typed)", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_zero_argument_typed : TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero (KExpr.app rfnz_motive rfnz_zero) :=
 @TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (KExpr.app rfnz_motive rfnz_zero)
  (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (rfnz_zero_typed (@ListType.nil KExpr)))
  (@DefEqIn.symm rfnz_env (KExpr.app rfnz_motive rfnz_zero) rfnz_nat (rfnz_motive_beta rfnz_zero))", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_minor_argument_typed : TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_minor rfnz_minor_type :=
 @TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_minor (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat)) rfnz_minor_type
  (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_minor (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat)) rfnz_minor_core_typed) rfnz_minor_type_conversion", "Constructive checked prerequisite for actual-name Nat.zero typing or its actual guarded caller; no new typing-result premise."),
    (r"def rfnz_input : KExpr := rfnz_rec_app (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor rfnz_zero", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_input_typed : TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_input rfnz_nat :=
 @TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_input (KExpr.app rfnz_motive rfnz_zero) rfnz_nat (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (rfnz_rec (Level.succ Level.zero)) rfnz_motive) rfnz_zero) rfnz_minor) rfnz_zero rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (rfnz_rec (Level.succ Level.zero)) rfnz_motive) rfnz_zero) rfnz_minor rfnz_minor_type (KExpr.pi rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero))) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (rfnz_rec (Level.succ Level.zero)) rfnz_motive) rfnz_zero (KExpr.app rfnz_motive rfnz_zero) (KExpr.pi rfnz_minor_type (KExpr.pi rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)))) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rec (Level.succ Level.zero)) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.pi rfnz_nat (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))))) (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rec (Level.succ Level.zero)) (rfnz_rec_type (Level.succ Level.zero)) (rfnz_rec_typed (Level.succ Level.zero))) rfnz_motive_argument_typed) rfnz_zero_argument_typed) rfnz_minor_argument_typed) (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (rfnz_zero_typed (@ListType.nil KExpr)))) (rfnz_motive_beta rfnz_zero)", "A genuinely typed universe-one actual-name Nat.rec input; the four-entry typing-environment source bridge remains separate."),
    (r"def rfnz_raw_result : KExpr :=
 KExpr.app (KExpr.app (KExpr.app
  (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs
   (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level)))
  rfnz_motive) rfnz_zero) rfnz_minor", "Exact model data used by the actual-name Nat.zero stored/instance typing and guarded caller."),
    (r"def rfnz_guarded_step : iota_step (red_rec rfnz_env) rfnz_input rfnz_raw_result :=
 iota_reduct_full_recon (red_rec rfnz_env) rfnz_input rfnz_raw_result
  fixture_nat_rec_name fixture_nat_rec_meta rfnz_zero fixture_nat_zero_name
  (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_rec_name))
  rfnz_actual_metadata
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero))
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_zero_name))
  rfnz_actual_zero_rule (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl KExpr rfnz_raw_result)", "The actual reflected guarded iota operation returns the once-instantiated raw zero-rule application, with actual lookup and guard proofs."),
    (r"def rfnz_raw_result_typed : TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_raw_result rfnz_nat :=
 @TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero) rfnz_nat (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (rfnz_rhs (Level.succ Level.zero)) rfnz_motive) rfnz_zero) rfnz_minor rfnz_minor_type (KExpr.app rfnz_motive rfnz_zero) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (rfnz_rhs (Level.succ Level.zero)) rfnz_motive) rfnz_zero (KExpr.app rfnz_motive rfnz_zero) (KExpr.pi rfnz_minor_type (KExpr.app rfnz_motive rfnz_zero)) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rhs (Level.succ Level.zero)) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero))) (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rhs (Level.succ Level.zero)) (rfnz_rule_type (Level.succ Level.zero)) (rfnz_actual_instance_typed (Level.succ Level.zero))) rfnz_motive_argument_typed) rfnz_zero_argument_typed) rfnz_minor_argument_typed) (rfnz_motive_beta rfnz_zero)", "Type the raw actual guarded result from derived instance typing and real arguments, not from a subject-reduction oracle."),
];

enum Registration {
    Data {
        declaration_index: usize,
        name: &'static str,
    },
    Proof {
        declaration_index: usize,
        name: &'static str,
        type_src: &'static str,
        value_src: &'static str,
    },
}

const REGISTRATIONS: &[Registration] = &[
    Registration::Data {
        declaration_index: 0,
        name: "rfnz_nat",
    },
    Registration::Data {
        declaration_index: 1,
        name: "rfnz_zero",
    },
    Registration::Data {
        declaration_index: 2,
        name: "rfnz_succ",
    },
    Registration::Data {
        declaration_index: 3,
        name: "rfnz_rec_signature",
    },
    Registration::Data {
        declaration_index: 4,
        name: "rfnz_parameter",
    },
    Registration::Data {
        declaration_index: 5,
        name: "rfnz_motive_type",
    },
    Registration::Data {
        declaration_index: 6,
        name: "rfnz_sarm",
    },
    Registration::Data {
        declaration_index: 7,
        name: "rfnz_rec_type",
    },
    Registration::Data {
        declaration_index: 8,
        name: "rfnz_rhs",
    },
    Registration::Proof {
        declaration_index: 9,
        name: "rfnz_parameter_list",
        type_src: r"@Eq (ListType Name) (kconst_params rfnz_rec_signature) (@ListType.cons Name rfnz_parameter (@ListType.nil Name))",
        value_src: r"@Eq.refl (ListType Name) (@ListType.cons Name rfnz_parameter (@ListType.nil Name))",
    },
    Registration::Proof {
        declaration_index: 10,
        name: "rfnz_signature_shape",
        type_src: r"@Eq KConstSig rfnz_rec_signature (KConstSig.mk (@ListType.cons Name rfnz_parameter (@ListType.nil Name)) (rfnz_rec_type (Level.param rfnz_parameter)))",
        value_src: r"@Eq.refl KConstSig rfnz_rec_signature",
    },
    Registration::Data {
        declaration_index: 11,
        name: "rfnz_tenv",
    },
    Registration::Proof {
        declaration_index: 12,
        name: "rfnz_nat_lookup",
        type_src: r"@Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv literal_builtin_nat_name (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
        value_src: r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))",
    },
    Registration::Proof {
        declaration_index: 13,
        name: "rfnz_zero_lookup",
        type_src: r"@Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv fixture_nat_zero_name (@ListType.nil Level)) (@OptionType.some KExpr rfnz_nat)",
        value_src: r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat)",
    },
    Registration::Proof {
        declaration_index: 14,
        name: "rfnz_succ_lookup",
        type_src: r"@Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv fixture_nat_succ_name (@ListType.nil Level)) (@OptionType.some KExpr (KExpr.pi rfnz_nat rfnz_nat))",
        value_src: r"@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi rfnz_nat rfnz_nat))",
    },
    Registration::Proof {
        declaration_index: 15,
        name: "rfnz_rec_lookup",
        type_src: r"forall (u : Level),
 @Eq (OptionType KExpr) (kdecl_type_at rfnz_tenv fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level))) (@OptionType.some KExpr (rfnz_rec_type u))",
        value_src: r"fun (u : Level) =>
 @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_rec_type u))",
    },
    Registration::Data {
        declaration_index: 16,
        name: "rfnz_rule_type",
    },
    Registration::Proof {
        declaration_index: 17,
        name: "rfnz_nat_typed",
        type_src: r"forall (G : ListType KExpr),
 TypingCtx rfnz_tenv G rfnz_nat (KExpr.sort (Level.succ Level.zero))",
        value_src: r"fun (G : ListType KExpr) =>
 @TypingCtx.const rfnz_tenv G literal_builtin_nat_name (@ListType.nil Level) (KExpr.sort (Level.succ Level.zero)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))))",
    },
    Registration::Proof {
        declaration_index: 18,
        name: "rfnz_zero_typed",
        type_src: r"forall (G : ListType KExpr),
 TypingCtx rfnz_tenv G rfnz_zero rfnz_nat",
        value_src: r"fun (G : ListType KExpr) =>
 @TypingCtx.const rfnz_tenv G fixture_nat_zero_name (@ListType.nil Level) rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat))",
    },
    Registration::Proof {
        declaration_index: 19,
        name: "rfnz_succ_typed",
        type_src: r"forall (G : ListType KExpr),
 TypingCtx rfnz_tenv G rfnz_succ (KExpr.pi rfnz_nat rfnz_nat)",
        value_src: r"fun (G : ListType KExpr) =>
 @TypingCtx.const rfnz_tenv G fixture_nat_succ_name (@ListType.nil Level) (KExpr.pi rfnz_nat rfnz_nat) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.pi rfnz_nat rfnz_nat)))",
    },
    Registration::Proof {
        declaration_index: 20,
        name: "rfnz_motive_typed",
        type_src: r"forall (u : Level) (G : ListType KExpr),
 TypingCtx rfnz_tenv G (rfnz_motive_type u) (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ u)))",
        value_src: r"fun (u : Level) (G : ListType KExpr) =>
 @TypingCtx.pi rfnz_tenv G rfnz_nat (KExpr.sort u) (Level.succ Level.zero) (Level.succ u) (rfnz_nat_typed G) (@TypingCtx.sort rfnz_tenv (@ListType.cons KExpr rfnz_nat G) u)",
    },
    Registration::Proof {
        declaration_index: 21,
        name: "rfnz_zero_domain_typed",
        type_src: r"forall (u : Level),
 TypingCtx rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.sort u)",
        value_src: r"fun (u : Level) =>
 (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) (KExpr.bvar Nat.zero) rfnz_zero rfnz_nat (KExpr.sort u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) Nat.zero (rfnz_motive_type u) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_motive_type u)))) (rfnz_zero_typed (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))",
    },
    Registration::Proof {
        declaration_index: 22,
        name: "rfnz_sarm_typed",
        type_src: r"forall (u : Level),
 TypingCtx rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))) rfnz_sarm (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.imax u u)))",
        value_src: r"fun (u : Level) =>
 @TypingCtx.pi rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))) rfnz_nat (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (Level.succ Level.zero) (Level.imax u u) (rfnz_nat_typed (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (@TypingCtx.pi rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) u u (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero) rfnz_nat (KExpr.sort u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (Nat.succ (Nat.succ Nat.zero)) (rfnz_motive_type u) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_motive_type u)))) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) Nat.zero rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat)))) (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))) rfnz_nat (KExpr.sort u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (rfnz_motive_type u) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (rfnz_motive_type u)))) (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)) rfnz_nat rfnz_nat (rfnz_succ_typed (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))))) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))))) (Nat.succ Nat.zero) rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat))))))",
    },
    Registration::Proof {
        declaration_index: 23,
        name: "rfnz_rhs_typed",
        type_src: r"forall (u : Level),
 TypingCtx rfnz_tenv (@ListType.nil KExpr) (rfnz_rhs u) (rfnz_rule_type u)",
        value_src: r"fun (u : Level) =>
 (@TypingCtx.lam rfnz_tenv (@ListType.nil KExpr) (rfnz_motive_type u) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.lam rfnz_sarm (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero))) (Level.imax (Level.succ Level.zero) (Level.succ u)) (rfnz_motive_typed u (@ListType.nil KExpr)) (@TypingCtx.lam rfnz_tenv (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.lam rfnz_sarm (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) u (rfnz_zero_domain_typed u) (@TypingCtx.lam rfnz_tenv (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr))) rfnz_sarm (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero) (Level.imax (Level.succ Level.zero) (Level.imax u u)) (rfnz_sarm_typed u) (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_sarm (@ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@ListType.cons KExpr (rfnz_motive_type u) (@ListType.nil KExpr)))) (Nat.succ Nat.zero) (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero)))))))",
    },
    Registration::Proof {
        declaration_index: 24,
        name: "rfnz_stored_rhs_shape",
        type_src: r"@Eq KExpr kcre_witness_nat_zero_rhs (rfnz_rhs (Level.param rfnz_parameter))",
        value_src: r"@Eq.refl KExpr kcre_witness_nat_zero_rhs",
    },
    Registration::Proof {
        declaration_index: 25,
        name: "rfnz_stored_rhs_typed",
        type_src: r"TypingCtx rfnz_tenv (@ListType.nil KExpr) kcre_witness_nat_zero_rhs (rfnz_rule_type (Level.param rfnz_parameter))",
        value_src: r"rfnz_rhs_typed (Level.param rfnz_parameter)",
    },
    Registration::Proof {
        declaration_index: 26,
        name: "rfnz_actual_metadata",
        type_src: r"@Eq (OptionType RecMeta) (recmeta_for (red_rec kernel_core_red_env) fixture_nat_rec_name) (@OptionType.some RecMeta fixture_nat_rec_meta)",
        value_src: r"@Eq.refl (OptionType RecMeta) (@OptionType.some RecMeta fixture_nat_rec_meta)",
    },
    Registration::Proof {
        declaration_index: 27,
        name: "rfnz_actual_zero_rule",
        type_src: r"@Eq (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name) (@OptionType.some RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs))",
        value_src: r"@Eq.refl (OptionType RecRule) (@OptionType.some RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs))",
    },
    Registration::Proof {
        declaration_index: 28,
        name: "rfnz_lookup_rhs_typed",
        type_src: r"forall (rule : RecRule)
 (h : @Eq (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name) (@OptionType.some RecRule rule)),
 TypingCtx rfnz_tenv (@ListType.nil KExpr) (recrule_rhs rule)
  (rfnz_rule_type (Level.param rfnz_parameter))",
        value_src: r"fun (rule : RecRule)
 (h : @Eq (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name) (@OptionType.some RecRule rule)) =>
 @Eq.rec RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  (fun (r : RecRule) (_eq : @Eq RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs) r) =>
   TypingCtx rfnz_tenv (@ListType.nil KExpr) (recrule_rhs r)
    (rfnz_rule_type (Level.param rfnz_parameter)))
  rfnz_stored_rhs_typed rule
  (Eq.symm RecRule rule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
   (option_some_inj RecRule rule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
    (Eq.trans (OptionType RecRule) (@OptionType.some RecRule rule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
     (@OptionType.some RecRule (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs))
     (Eq.symm (OptionType RecRule) (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name) (@OptionType.some RecRule rule) h)
     rfnz_actual_zero_rule)))",
    },
    Registration::Proof {
        declaration_index: 29,
        name: "rfnz_rec_signature_supported",
        type_src: r"KExprParamSupport (kconst_params rfnz_rec_signature) (kconst_type rfnz_rec_signature)",
        value_src: r"(@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.sort (Level.param rfnz_parameter))) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const fixture_nat_zero_name (@ListType.nil Level))) (KExpr.pi (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.sort (Level.param rfnz_parameter)) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.sort (kconst_params rfnz_rec_signature) (Level.param rfnz_parameter) (@LevelParamSupport.param (kconst_params rfnz_rec_signature) rfnz_parameter Nat.zero (@Eq.refl (OptionType Nat) (@OptionType.some Nat Nat.zero))))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.app (KExpr.bvar Nat.zero) (KExpr.const fixture_nat_zero_name (@ListType.nil Level))) (KExpr.pi (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar Nat.zero) (KExpr.const fixture_nat_zero_name (@ListType.nil Level)) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) Nat.zero) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) fixture_nat_zero_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature)))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (KExpr.pi (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))))) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ (Nat.succ Nat.zero))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) Nat.zero)) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.const fixture_nat_succ_name (@ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) fixture_nat_succ_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ Nat.zero)))))) (@KExprParamSupport.pi (kconst_params rfnz_rec_signature) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)) (@KExprParamSupport.const (kconst_params rfnz_rec_signature) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (kconst_params rfnz_rec_signature))) (@KExprParamSupport.app (kconst_params rfnz_rec_signature) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (@KExprParamSupport.bvar (kconst_params rfnz_rec_signature) Nat.zero))))))",
    },
    Registration::Proof {
        declaration_index: 30,
        name: "rfnz_tenv_extend_supported",
        type_src: r"forall (key : Name) (sig : KConstSig) (rest : KDeclEnv)
 (hs : KExprParamSupport (kconst_params sig) (kconst_type sig))
 (hr : KDeclEnvTypeParamSupported rest),
 KDeclEnvTypeParamSupported (fun (n : Name) => opt_pick KConstSig (name_eqb n key) sig (rest n))",
        value_src: r"fun (key : Name) (sig : KConstSig) (rest : KDeclEnv)
 (hs : KExprParamSupport (kconst_params sig) (kconst_type sig))
 (hr : KDeclEnvTypeParamSupported rest) =>
 fun (query : Name) (selected : KConstSig)
 (found : @Eq (OptionType KConstSig) (opt_pick KConstSig (name_eqb query key) sig (rest query)) (@OptionType.some KConstSig selected)) =>
 opt_pick_some_inv KConstSig (name_eqb query key) sig (rest query) selected
  (KExprParamSupport (kconst_params selected) (kconst_type selected)) found
  (fun (_matched : @Eq Bool (name_eqb query key) Bool.true) (same : @Eq KConstSig sig selected) =>
   Eq.subst KConstSig (fun (entry : KConstSig) => KExprParamSupport (kconst_params entry) (kconst_type entry)) sig selected same hs)
  (fun (_missed : @Eq Bool (name_eqb query key) Bool.false)
   (tail : @Eq (OptionType KConstSig) (rest query) (@OptionType.some KConstSig selected)) =>
   hr query selected tail)",
    },
    Registration::Proof {
        declaration_index: 31,
        name: "rfnz_tenv_supported",
        type_src: r"KDeclEnvTypeParamSupported rfnz_tenv",
        value_src: r"rfnz_tenv_extend_supported literal_builtin_nat_name (KConstSig.mk (@ListType.nil Name) (KExpr.sort (Level.succ Level.zero))) (fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_zero_name) (KConstSig.mk (@ListType.nil Name) rfnz_nat) ((fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_succ_name) (KConstSig.mk (@ListType.nil Name) (KExpr.pi rfnz_nat rfnz_nat)) ((fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_rec_name) rfnz_rec_signature (@OptionType.none KConstSig)) n)) n))
  (@KExprParamSupport.sort (@ListType.nil Name) (Level.succ Level.zero) (@LevelParamSupport.succ (@ListType.nil Name) Level.zero (@LevelParamSupport.zero (@ListType.nil Name))))
  (rfnz_tenv_extend_supported fixture_nat_zero_name (KConstSig.mk (@ListType.nil Name) rfnz_nat) (fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_succ_name) (KConstSig.mk (@ListType.nil Name) (KExpr.pi rfnz_nat rfnz_nat)) ((fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_rec_name) rfnz_rec_signature (@OptionType.none KConstSig)) n))
   (@KExprParamSupport.const (@ListType.nil Name) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (@ListType.nil Name)))
   (rfnz_tenv_extend_supported fixture_nat_succ_name (KConstSig.mk (@ListType.nil Name) (KExpr.pi rfnz_nat rfnz_nat)) (fun (n : Name) => opt_pick KConstSig (name_eqb n fixture_nat_rec_name) rfnz_rec_signature (@OptionType.none KConstSig))
    (@KExprParamSupport.pi (@ListType.nil Name) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (KExpr.const literal_builtin_nat_name (@ListType.nil Level)) (@KExprParamSupport.const (@ListType.nil Name) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (@ListType.nil Name))) (@KExprParamSupport.const (@ListType.nil Name) literal_builtin_nat_name (@ListType.nil Level) (@LevelListParamSupport.nil (@ListType.nil Name))))
    (kdecl_env_type_param_supported_singleton fixture_nat_rec_name rfnz_rec_signature rfnz_rec_signature_supported)))",
    },
    Registration::Proof {
        declaration_index: 32,
        name: "rfnz_rhs_instance_shape",
        type_src: r"forall (u : Level),
 @Eq KExpr
 (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))
 (rfnz_rhs u)",
        value_src: r"fun (u : Level) =>
 @Eq.refl KExpr (rfnz_rhs u)",
    },
    Registration::Proof {
        declaration_index: 33,
        name: "rfnz_rule_type_instance_shape",
        type_src: r"forall (u : Level),
 @Eq KExpr
 (instLevels (kconst_params rfnz_rec_signature) (rfnz_rule_type (Level.param rfnz_parameter)) (@ListType.cons Level u (@ListType.nil Level)))
 (rfnz_rule_type u)",
        value_src: r"fun (u : Level) =>
 @Eq.refl KExpr (rfnz_rule_type u)",
    },
    Registration::Proof {
        declaration_index: 34,
        name: "rfnz_lookup_instance_typed",
        type_src: r"forall (rule : RecRule)
 (found : @Eq (OptionType RecRule)
  (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
  (@OptionType.some RecRule rule)) (u : Level),
 TypingCtx rfnz_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance rfnz_rec_signature (recrule_rhs rule) (@ListType.cons Level u (@ListType.nil Level)))
  (rfnz_rule_type u)",
        value_src: r"fun (rule : RecRule)
 (found : @Eq (OptionType RecRule)
  (recrule_for (red_rec kernel_core_red_env) fixture_nat_rec_name fixture_nat_zero_name)
  (@OptionType.some RecRule rule)) (u : Level) =>
 typingctx_instLevels rfnz_tenv rfnz_tenv_supported
  (kconst_params rfnz_rec_signature) (@ListType.cons Level u (@ListType.nil Level))
  (@ListType.nil KExpr) (recrule_rhs rule) (rfnz_rule_type (Level.param rfnz_parameter))
  (rfnz_lookup_rhs_typed rule found)",
    },
    Registration::Proof {
        declaration_index: 35,
        name: "rfnz_actual_instance_typed",
        type_src: r"forall (u : Level),
 TypingCtx rfnz_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))
  (rfnz_rule_type u)",
        value_src: r"fun (u : Level) =>
 rfnz_lookup_instance_typed (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  rfnz_actual_zero_rule u",
    },
    Registration::Proof {
        declaration_index: 36,
        name: "rfnz_self_parameter_instance_typed",
        type_src: r"TypingCtx rfnz_tenv (@ListType.nil KExpr)
  (recursor_rhs_instance rfnz_rec_signature kcre_witness_nat_zero_rhs
   (@ListType.cons Level (Level.succ (Level.param rfnz_parameter)) (@ListType.nil Level)))
  (rfnz_rule_type (Level.succ (Level.param rfnz_parameter)))",
        value_src: r"rfnz_actual_instance_typed (Level.succ (Level.param rfnz_parameter))",
    },
    Registration::Data {
        declaration_index: 37,
        name: "rfnz_rec",
    },
    Registration::Proof {
        declaration_index: 38,
        name: "rfnz_rec_typed",
        type_src: r"forall (u : Level),
 TypingCtx rfnz_tenv (@ListType.nil KExpr) (rfnz_rec u) (rfnz_rec_type u)",
        value_src: r"fun (u : Level) =>
 @TypingCtx.const rfnz_tenv (@ListType.nil KExpr) fixture_nat_rec_name
  (@ListType.cons Level u (@ListType.nil Level)) (rfnz_rec_type u) (rfnz_rec_lookup u)",
    },
    Registration::Data {
        declaration_index: 39,
        name: "rfnz_rec_app",
    },
    Registration::Data {
        declaration_index: 40,
        name: "rfnz_env",
    },
    Registration::Data {
        declaration_index: 41,
        name: "rfnz_motive",
    },
    Registration::Data {
        declaration_index: 42,
        name: "rfnz_minor",
    },
    Registration::Data {
        declaration_index: 43,
        name: "rfnz_minor_type",
    },
    Registration::Proof {
        declaration_index: 44,
        name: "rfnz_motive_core_typed",
        type_src: r"TypingCtx rfnz_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero))",
        value_src: r"@TypingCtx.lam rfnz_tenv (@ListType.nil KExpr) rfnz_nat rfnz_nat (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero)
 (rfnz_nat_typed (@ListType.nil KExpr)) (rfnz_nat_typed (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr)))",
    },
    Registration::Proof {
        declaration_index: 45,
        name: "rfnz_minor_core_typed",
        type_src: r"TypingCtx rfnz_tenv (@ListType.nil KExpr) rfnz_minor (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat))",
        value_src: r"@TypingCtx.lam rfnz_tenv (@ListType.nil KExpr) rfnz_nat (KExpr.lam rfnz_nat (KExpr.app rfnz_succ (KExpr.bvar Nat.zero))) (KExpr.pi rfnz_nat rfnz_nat) (Level.succ Level.zero)
 (rfnz_nat_typed (@ListType.nil KExpr))
 (@TypingCtx.lam rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr)) rfnz_nat (KExpr.app rfnz_succ (KExpr.bvar Nat.zero)) rfnz_nat (Level.succ Level.zero)
  (rfnz_nat_typed (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr)))
  (@TypingCtx.app rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr))) rfnz_succ (KExpr.bvar Nat.zero) rfnz_nat rfnz_nat
   (rfnz_succ_typed (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr))))
   (@TypingCtx.var rfnz_tenv (@ListType.cons KExpr rfnz_nat (@ListType.cons KExpr rfnz_nat (@ListType.nil KExpr))) Nat.zero rfnz_nat (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_nat)))))",
    },
    Registration::Proof {
        declaration_index: 46,
        name: "rfnz_motive_beta",
        type_src: r"forall (x : KExpr),
 DefEqIn rfnz_env (KExpr.app rfnz_motive x) rfnz_nat",
        value_src: r"fun (x : KExpr) =>
 def_eq_in_beta rfnz_env rfnz_nat rfnz_nat x",
    },
    Registration::Proof {
        declaration_index: 47,
        name: "rfnz_minor_type_conversion",
        type_src: r"DefEqIn rfnz_env (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat)) rfnz_minor_type",
        value_src: r"@DefEqIn.pi rfnz_env rfnz_nat rfnz_nat (KExpr.pi rfnz_nat rfnz_nat) (KExpr.pi (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) (KExpr.app rfnz_motive (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))))
  (@DefEqIn.refl rfnz_env rfnz_nat)
  (@DefEqIn.pi rfnz_env rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) rfnz_nat (KExpr.app rfnz_motive (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))
   (@DefEqIn.symm rfnz_env (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) rfnz_nat (rfnz_motive_beta (KExpr.bvar Nat.zero)))
   (@DefEqIn.symm rfnz_env (KExpr.app rfnz_motive (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) rfnz_nat (rfnz_motive_beta (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))))",
    },
    Registration::Proof {
        declaration_index: 48,
        name: "rfnz_motive_argument_typed",
        type_src: r"TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero))",
        value_src: r"(nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) rfnz_motive_core_typed)",
    },
    Registration::Proof {
        declaration_index: 49,
        name: "rfnz_zero_argument_typed",
        type_src: r"TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero (KExpr.app rfnz_motive rfnz_zero)",
        value_src: r"@TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (KExpr.app rfnz_motive rfnz_zero)
  (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (rfnz_zero_typed (@ListType.nil KExpr)))
  (@DefEqIn.symm rfnz_env (KExpr.app rfnz_motive rfnz_zero) rfnz_nat (rfnz_motive_beta rfnz_zero))",
    },
    Registration::Proof {
        declaration_index: 50,
        name: "rfnz_minor_argument_typed",
        type_src: r"TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_minor rfnz_minor_type",
        value_src: r"@TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_minor (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat)) rfnz_minor_type
  (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_minor (KExpr.pi rfnz_nat (KExpr.pi rfnz_nat rfnz_nat)) rfnz_minor_core_typed) rfnz_minor_type_conversion",
    },
    Registration::Data {
        declaration_index: 51,
        name: "rfnz_input",
    },
    Registration::Proof {
        declaration_index: 52,
        name: "rfnz_input_typed",
        type_src: r"TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_input rfnz_nat",
        value_src: r"@TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_input (KExpr.app rfnz_motive rfnz_zero) rfnz_nat (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (rfnz_rec (Level.succ Level.zero)) rfnz_motive) rfnz_zero) rfnz_minor) rfnz_zero rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (rfnz_rec (Level.succ Level.zero)) rfnz_motive) rfnz_zero) rfnz_minor rfnz_minor_type (KExpr.pi rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero))) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (rfnz_rec (Level.succ Level.zero)) rfnz_motive) rfnz_zero (KExpr.app rfnz_motive rfnz_zero) (KExpr.pi rfnz_minor_type (KExpr.pi rfnz_nat (KExpr.app rfnz_motive (KExpr.bvar Nat.zero)))) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rec (Level.succ Level.zero)) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.pi rfnz_nat (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))))) (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rec (Level.succ Level.zero)) (rfnz_rec_type (Level.succ Level.zero)) (rfnz_rec_typed (Level.succ Level.zero))) rfnz_motive_argument_typed) rfnz_zero_argument_typed) rfnz_minor_argument_typed) (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (rfnz_zero_typed (@ListType.nil KExpr)))) (rfnz_motive_beta rfnz_zero)",
    },
    Registration::Data {
        declaration_index: 53,
        name: "rfnz_raw_result",
    },
    Registration::Proof {
        declaration_index: 54,
        name: "rfnz_guarded_step",
        type_src: r"iota_step (red_rec rfnz_env) rfnz_input rfnz_raw_result",
        value_src: r"iota_reduct_full_recon (red_rec rfnz_env) rfnz_input rfnz_raw_result
  fixture_nat_rec_name fixture_nat_rec_meta rfnz_zero fixture_nat_zero_name
  (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_rec_name))
  rfnz_actual_metadata
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero))
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_zero_name))
  rfnz_actual_zero_rule (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl KExpr rfnz_raw_result)",
    },
    Registration::Proof {
        declaration_index: 55,
        name: "rfnz_raw_result_typed",
        type_src: r"TypingCtxConvIn rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_raw_result rfnz_nat",
        value_src: r"@TypingCtxConvIn.conv rfnz_env rfnz_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero) rfnz_nat (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (KExpr.app (rfnz_rhs (Level.succ Level.zero)) rfnz_motive) rfnz_zero) rfnz_minor rfnz_minor_type (KExpr.app rfnz_motive rfnz_zero) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (KExpr.app (rfnz_rhs (Level.succ Level.zero)) rfnz_motive) rfnz_zero (KExpr.app rfnz_motive rfnz_zero) (KExpr.pi rfnz_minor_type (KExpr.app rfnz_motive rfnz_zero)) (@TypingCtxConvIn.app rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rhs (Level.succ Level.zero)) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero))) (nz_typing_to_semantic rfnz_env rfnz_tenv (@ListType.nil KExpr) (rfnz_rhs (Level.succ Level.zero)) (rfnz_rule_type (Level.succ Level.zero)) (rfnz_actual_instance_typed (Level.succ Level.zero))) rfnz_motive_argument_typed) rfnz_zero_argument_typed) rfnz_minor_argument_typed) (rfnz_motive_beta rfnz_zero)",
    },
];

fn checked_definition(
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> SpecDefinition {
    SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    }
}

impl Specification {
    /// Requires actual kernel_core_red_env data and semantic fixture aliases,
    /// typingctx_instLevels, semantic_typing_universe_instantiation support
    /// helpers, acceptance_in, canonical iota_reduct_full_recon and the existing
    /// nz_typing_to_semantic embedding from add_nat_zero_rhs_typing.
    pub(super) fn add_reflected_nat_zero_typing(&mut self) -> Result<(), SpecError> {
        for registration in REGISTRATIONS {
            match registration {
                Registration::Data {
                    declaration_index,
                    name,
                } => {
                    let (source, description) = DECLARATIONS[*declaration_index];
                    self.add_recursive_def(source, description)?;
                    debug_assert!(self.definitions().contains_key(*name));
                }
                Registration::Proof {
                    declaration_index,
                    name,
                    type_src,
                    value_src,
                } => {
                    self.add_definition(checked_definition(
                        name,
                        type_src,
                        value_src,
                        DECLARATIONS[*declaration_index].1,
                    ))?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "reflected_nat_zero_typing_tests.rs"]
mod tests;
