// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Test-only role inventory and deliberately false registration bodies.

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "dia_entries_sound",
    "dia_stored_constant_admission",
    "dia_stored_constant_prior_sound",
    "dia_stored_family_prior_sound",
    "dia_input_admitted",
    "dia_input_to_old_chain",
    "dia_old_chain_trans",
    "dia_chain_to_old_chain",
    "dia_input_preserves_sound",
    "dia_chain_admitted",
    "dia_chain_sound",
    "dia_fresh_family",
    "dia_fresh_constant",
    "dia_reuse_family",
    "dia_reuse_constant",
    "dia_mixed_chain",
    "dia_mixed_admissions",
    "dia_mixed_preservation",
    "dia_reused_family_admitted",
    "dia_reused_constant_admitted",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[
    "dia_entries_sound",
    "dia_stored_constant_admission",
    "dia_stored_constant_prior_sound",
    "dia_stored_family_prior_sound",
    "dia_input_admitted",
    "dia_input_to_old_chain",
    "dia_old_chain_trans",
    "dia_chain_to_old_chain",
    "dia_input_preserves_sound",
    "dia_chain_admitted",
    "dia_chain_sound",
    "dia_fresh_family",
    "dia_fresh_constant",
    "dia_reuse_family",
    "dia_reuse_constant",
    "dia_mixed_chain",
    "dia_mixed_admissions",
    "dia_mixed_preservation",
    "dia_reused_family_admitted",
    "dia_reused_constant_admitted",
];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "dia_admission_at",
    "dia_requests_admitted",
    "dia_family_request",
    "dia_constant_request",
    "dia_mixed_requests",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[
    "KernelDeclInput",
    "KernelDeclInputAdmission",
    "KernelDeclInputAccepts",
    "KernelDeclInputChain",
];

// Owned false bodies are never visited by the production registrar.
#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "dia_false_constant_kind",
        r"KernelDeclInputAccepts env_freshness_const_result
 (KernelDeclInput.const_ ConstExtensionKind.opaque_ env_freshness_two env_freshness_type (KExpr.sort Level.zero))
 env_freshness_const_result",
        "dia_reuse_constant",
    ),
    (
        "dia_false_constant_type",
        r"KernelDeclInputAccepts env_freshness_const_result
 (KernelDeclInput.const_ ConstExtensionKind.reducible_ env_freshness_two (KExpr.sort Level.zero) (KExpr.sort Level.zero))
 env_freshness_const_result",
        "dia_reuse_constant",
    ),
    (
        "dia_false_constant_value",
        r"KernelDeclInputAccepts env_freshness_const_result
 (KernelDeclInput.const_ ConstExtensionKind.reducible_ env_freshness_two env_freshness_type env_freshness_type)
 env_freshness_const_result",
        "dia_reuse_constant",
    ),
    (
        "dia_false_family_type",
        r"KernelDeclInputAccepts env_freshness_const_result
 (KernelDeclInput.inductive_ Nat.zero Nat.zero (KExpr.sort Level.zero) (env_freshness_ctors env_freshness_one))
 env_freshness_const_result",
        "dia_reuse_family",
    ),
    (
        "dia_false_family_parameters",
        r"KernelDeclInputAccepts env_freshness_const_result
 (KernelDeclInput.inductive_ Nat.zero env_freshness_one env_freshness_type (env_freshness_ctors env_freshness_one))
 env_freshness_const_result",
        "dia_reuse_family",
    ),
    (
        "dia_false_family_constructors",
        r"KernelDeclInputAccepts env_freshness_const_result
 (KernelDeclInput.inductive_ Nat.zero Nat.zero env_freshness_type CtorDecls.nil) env_freshness_const_result",
        "dia_reuse_family",
    ),
    (
        "dia_false_reuse_position",
        r"Eq (OptionType KEnv) (sfa_entry_at env_freshness_const_result Nat.zero)
 (OptionType.some KEnv env_freshness_first)",
        r"Eq.refl (OptionType KEnv) (OptionType.some KEnv env_freshness_first)",
    ),
    (
        "dia_false_nonempty_nil",
        r"KernelDeclInputChain env_freshness_const_result
 (ListType.cons KernelDeclInput dia_family_request (ListType.nil KernelDeclInput)) env_freshness_const_result",
        "KernelDeclInputChain.nil env_freshness_const_result",
    ),
    (
        "dia_false_admission_body",
        "KernelDeclInputAdmission dia_constant_request",
        "dia_reused_family_admitted",
    ),
];
