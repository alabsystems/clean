// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::checks::{caller, computes};
use super::{ADMITTED_TYPE, CHAIN_SOUND_TYPE};
use crate::test_utils::{run_with_stack, shared_spec};

#[test]
fn declaration_input_admission_computed_payloads_and_history() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (source, expected) in [
            ("dia_family_request", "KernelDeclInput.inductive_ Nat.zero Nat.zero env_freshness_type (env_freshness_ctors env_freshness_one)"),
            ("dia_constant_request", "KernelDeclInput.const_ ConstExtensionKind.reducible_ env_freshness_two env_freshness_type (KExpr.sort Level.zero)"),
            ("sfa_entry_at env_freshness_const_result Nat.zero", "OptionType.some KEnv env_freshness_const_result"),
            ("sfa_entry_at env_freshness_const_result env_freshness_one", "OptionType.some KEnv env_freshness_first"),
            ("sfa_entry_at env_freshness_const_result env_freshness_two", "OptionType.none KEnv"),
            ("dia_admission_at KEnv.empty dia_family_request", "InductiveExtension KEnv.empty env_freshness_first"),
            ("dia_admission_at env_freshness_first dia_constant_request", "ConstantExtension env_freshness_first env_freshness_const_result"),
            ("dia_requests_admitted (ListType.nil KernelDeclInput)", "Nat"),
            ("dia_requests_admitted (ListType.cons KernelDeclInput dia_family_request (ListType.nil KernelDeclInput))", "ProdType (KernelDeclInputAdmission dia_family_request) Nat"),
        ] {
            computes(spec, source, expected);
        }
        computes(
            spec,
            "dia_mixed_requests",
            r"ListType.cons KernelDeclInput dia_family_request
 (ListType.cons KernelDeclInput dia_constant_request
  (ListType.cons KernelDeclInput dia_family_request
   (ListType.cons KernelDeclInput dia_constant_request (ListType.nil KernelDeclInput))))",
        );
    });
}

#[test]
fn declaration_input_admission_mixed_requests_and_preservation() {
    run_with_stack(|| {
        let spec = shared_spec();
        caller(spec, "dia_input_admitted", ADMITTED_TYPE);
        caller(spec, "dia_chain_sound", CHAIN_SOUND_TYPE);
        caller(
            spec,
            "dia_mixed_chain",
            "KernelDeclInputChain KEnv.empty dia_mixed_requests env_freshness_const_result",
        );
        caller(
            spec,
            "dia_mixed_admissions",
            "dia_requests_admitted dia_mixed_requests",
        );
        caller(
            spec,
            r"dia_chain_sound KEnv.empty dia_mixed_requests env_freshness_const_result KernelLocalCtx.nil
 dia_mixed_chain KernelInitialStateValid (DefinitionalExtension.refl KEnv.empty)",
            r"ProdType (KernelStateMatchesSpec (KernelState.mk env_freshness_const_result KernelLocalCtx.nil))
 (ProdType (EnvSound env_freshness_const_result) (dia_requests_admitted dia_mixed_requests))",
        );
        caller(spec, "dia_chain_to_old_chain KEnv.empty dia_mixed_requests env_freshness_const_result dia_mixed_chain", "KernelAddDeclChain KEnv.empty env_freshness_const_result");
        // This is erasure only: retaining the independent nonempty input trace
        // above is what prevents old refl from validating arbitrary requests.
        caller(spec, "dia_input_to_old_chain env_freshness_const_result dia_family_request env_freshness_const_result dia_reuse_family", "KernelAddDeclChain env_freshness_const_result env_freshness_const_result");
    });
}

#[test]
fn declaration_input_admission_consumes_valid_historical_witnesses() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (input, proof) in [
            ("dia_family_request", "dia_reused_family_admitted"),
            ("dia_constant_request", "dia_reused_constant_admitted"),
        ] {
            // Consume all three witness fields, especially EnvSound prior.
            // C is Type-valued, matching the genuine admission carrier.
            let source = format!(
                r"fun (C : Type)
 (k : forall (prior : KEnv), EnvSound prior -> dia_admission_at prior {input} -> C) =>
 KernelDeclInputAdmission.rec {input} (fun (_ : KernelDeclInputAdmission {input}) => C)
  (fun (prior : KEnv) (sound : EnvSound prior) (admitted : dia_admission_at prior {input}) =>
   k prior sound admitted) {proof}"
            );
            let ty = format!("forall (C : Type), (forall (prior : KEnv), EnvSound prior -> dia_admission_at prior {input} -> C) -> C");
            caller(spec, &source, &ty);
        }
        caller(
            spec,
            r"dia_stored_constant_prior_sound env_freshness_const_result Nat.zero env_freshness_first
 ConstExtensionKind.reducible_ env_freshness_two env_freshness_type (KExpr.sort Level.zero)
 env_freshness_const_preserves_sound (Eq.refl (OptionType KEnv) (OptionType.some KEnv env_freshness_const_result))",
            "EnvSound env_freshness_first",
        );
        caller(
            spec,
            r"dia_stored_family_prior_sound env_freshness_const_result env_freshness_one KEnv.empty
 Nat.zero Nat.zero env_freshness_type (env_freshness_ctors env_freshness_one)
 env_freshness_const_preserves_sound (Eq.refl (OptionType KEnv) (OptionType.some KEnv env_freshness_first))",
            "EnvSound KEnv.empty",
        );
    });
}

#[test]
fn declaration_input_admission_opaque_constant_fresh_and_reuse() {
    run_with_stack(|| {
        let spec = shared_spec();
        let input = "KernelDeclInput.const_ ConstExtensionKind.opaque_ env_freshness_two env_freshness_type (KExpr.sort Level.zero)";
        let out = "KEnv.addConst env_freshness_first ConstExtensionKind.opaque_ env_freshness_two env_freshness_type (KExpr.sort Level.zero)";
        let extension = r"ConstantExtension.mk env_freshness_first ConstExtensionKind.opaque_ env_freshness_two
 env_freshness_type (KExpr.sort Level.zero) (Level.succ (Level.succ Level.zero))
 (Eq.refl Bool Bool.true) (Typing.sort (Level.succ Level.zero)) (Typing.sort Level.zero)";
        let fresh = format!("KernelDeclInputAccepts.const_fresh env_freshness_first ConstExtensionKind.opaque_ env_freshness_two env_freshness_type (KExpr.sort Level.zero) ({extension})");
        caller(
            spec,
            &fresh,
            &format!("KernelDeclInputAccepts env_freshness_first ({input}) ({out})"),
        );
        let sound = format!("dia_input_preserves_sound env_freshness_first ({input}) ({out}) ({fresh}) env_freshness_first_sound");
        let reuse = format!("KernelDeclInputAccepts.const_reuse ({out}) Nat.zero env_freshness_first ConstExtensionKind.opaque_ env_freshness_two env_freshness_type (KExpr.sort Level.zero) (Eq.refl (OptionType KEnv) (OptionType.some KEnv ({out})))");
        caller(
            spec,
            &format!("dia_input_admitted ({out}) ({input}) ({out}) ({reuse}) ({sound})"),
            &format!("KernelDeclInputAdmission ({input})"),
        );
    });
}
