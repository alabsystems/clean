// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Forged statements and computational cases for the CIC_L qualification.

/// The forged-statement controls: `(namespace, proof, wrong)`. The proof of
/// `CICL.<namespace>.<proof>` is re-entered at its own statement, which must
/// pass, and at the proposition `CICL.<namespace>.<wrong>`, which must fail with
/// a type mismatch. Every `wrong*` proposition the theory declares has a row
/// here, and every row names one ([`super::forged_row_gaps`]).
pub(super) const FORGED_ROWS: &[(&str, &str, &str)] = &[
    (
        "TypedSignatureCases",
        "empty_admitted",
        "wrongStageAdmission",
    ),
    (
        "TypedSignatureCases",
        "bound_variable_has_no_family_occurrence",
        "wrongHeaderOccurrence",
    ),
    (
        "DeclarationCases",
        "theorem_delta_available",
        "wrongOpaqueDelta",
    ),
    (
        "DeclarationCases",
        "theorem_admitted",
        "wrongPrimitiveAdmission",
    ),
    (
        "DeclarationCases",
        "theorem_admitted",
        "wrongUnsafeAdmission",
    ),
    (
        "DeclarationCases",
        "theorem_admitted",
        "wrongPartialAdmission",
    ),
    ("LevelCases", "imax_kills_left", "wrongImax"),
    ("LevelCases", "simultaneous", "wrongSimultaneous"),
    ("ExprCases", "binder_levels", "wrongBinder"),
    ("ExprCases", "metadata_payload", "wrongMetadata"),
    ("ExprCases", "let_hint_preserved", "wrongLetHint"),
    ("SubstitutionCases", "avoids_capture", "wrongCapture"),
    (
        "SubstitutionCases",
        "preserves_bound_zero",
        "wrongBoundZero",
    ),
    (
        "SubstitutionCases",
        "decrements_outer_index",
        "wrongOuterIndex",
    ),
    ("SubstitutionCases", "traverses_let_hint", "wrongLetSkip"),
    (
        "SubstitutionCases",
        "traverses_metadata_projection",
        "wrongDropMetadata",
    ),
    ("HeaderTraceCases", "delta_step", "wrongAliasResult"),
    ("HeaderTraceCases", "alias_header_view", "wrongAliasHeader"),
    (
        "MutualHeaderCases",
        "header_certificate_exists",
        "wrongEmptyBlock",
    ),
    (
        "MutualHeaderCases",
        "empty_admitted",
        "wrongMutualAdmission",
    ),
    (
        "MutualHeaderCases",
        "indexed_header_count",
        "wrongIndexCount",
    ),
    ("MutualHeaderCases", "empty_admitted", "wrongBatchAdmission"),
    (
        "MutualHeaderCases",
        "full_headers_lookup",
        "wrongMissingHeader",
    ),
    ("Level", "ground_proposition_bound", "wrongVariableBound"),
    (
        "ConstructorChecksCases",
        "constructor_metadata",
        "wrongOrdinal",
    ),
    (
        "ConstructorChecksCases",
        "constructor_metadata",
        "wrongFieldCount",
    ),
    (
        "ConstructorChecksCases",
        "shared_parameter_checked",
        "wrongUniformParameter",
    ),
    (
        "ConstructorChecksCases",
        "f_result_shape",
        "wrongReturnFamily",
    ),
    (
        "ConstructorChecksCases",
        "mutual_field_positive",
        "wrongRecursiveParameter",
    ),
    (
        "ConstructorChecksCases",
        "function_field_positive",
        "wrongNegativeField",
    ),
    (
        "ConstructorChecksCases",
        "empty_admitted",
        "wrongConstructorStage",
    ),
    (
        "ConstructorChecksCases",
        "f_constructor_lookup",
        "wrongMissingConstructor",
    ),
    ("CoreTypingCases", "identity_typed", "wrongOpenTyping"),
    ("CoreTypingCases", "let_typed", "wrongLetHint"),
    ("CoreTypingCases", "reflexivity", "wrongOpenEquality"),
    ("CoreTypingCases", "polymorphic_typed", "wrongArity"),
    ("CoreTypingCases", "beta_rule", "wrongBetaWithoutArgument"),
    (
        "SignatureCases",
        "old_proposition_preserved",
        "wrongDuplicate",
    ),
    (
        "SignatureCases",
        "proposition_admission",
        "wrongOpenAdmission",
    ),
    (
        "SignatureCases",
        "polymorphic_admission",
        "wrongLevelAdmission",
    ),
    ("SignatureCases", "identity_admission", "wrongBodyAdmission"),
    ("SignatureCases", "proposition_signature", "wrongHistory"),
    (
        "SignatureCases",
        "identity_admission",
        "wrongForwardAdmission",
    ),
    (
        "UniverseTypingCases",
        "polymorphic_body_instantiated",
        "wrongSortType",
    ),
    (
        "UniverseTypingCases",
        "beta_instantiated",
        "wrongBetaResult",
    ),
    (
        "UniverseTypingCases",
        "local_definition_instantiated",
        "wrongLocalType",
    ),
    (
        "UniverseTypingCases",
        "delta_instantiated",
        "wrongDeltaArgument",
    ),
    (
        "UniverseTypingCases",
        "polymorphic_constant_instantiated",
        "wrongArity",
    ),
    (
        "UniverseTypingCases",
        "instantiated_type_scoped",
        "wrongScope",
    ),
    (
        "ContextRenamingCases",
        "outer_variable_shifted",
        "wrongOuterIndex",
    ),
    (
        "ContextRenamingCases",
        "bound_variable_preserved",
        "wrongCapturedBinder",
    ),
    (
        "ContextRenamingCases",
        "dependent_beta_shifted",
        "wrongBetaIndex",
    ),
    (
        "ContextRenamingCases",
        "lifted_definition_embedding",
        "wrongLocalValue",
    ),
    (
        "ContextRenamingCases",
        "closed_delta_preserved",
        "wrongGlobalName",
    ),
    (
        "ContextRenamingCases",
        "closed_body_unchanged",
        "wrongClosedBody",
    ),
    (
        "ContextRenamingCases",
        "closed_signature",
        "wrongGlobalAdmission",
    ),
    (
        "EqualityConversionCases",
        "beta_converted",
        "wrongTargetSort",
    ),
    ("EqualityConversionCases", "beta_converted", "wrongEndpoint"),
    (
        "EqualityConversionCases",
        "type_equality",
        "wrongTypeEquality",
    ),
    (
        "EqualityConversionCases",
        "converted_right_endpoint",
        "wrongEndpointTyping",
    ),
    (
        "TypedSubstitutionCases",
        "open_argument_avoids_capture",
        "wrongCapture",
    ),
    (
        "TypedSubstitutionCases",
        "open_argument_avoids_capture",
        "wrongResultType",
    ),
    (
        "TypedSubstitutionCases",
        "beta_result_from_body",
        "wrongBetaResult",
    ),
    (
        "TypedSubstitutionCases",
        "let_result_from_body",
        "wrongLetResult",
    ),
    (
        "TypedSubstitutionCases",
        "typed_sort_mapping",
        "wrongArgumentType",
    ),
    (
        "TypedSubstitutionCases",
        "correct_definition_mapping",
        "wrongDefinitionValue",
    ),
    (
        "TypedSubstitutionCases",
        "eliminates_two_binders",
        "wrongComposition",
    ),
    (
        "TypeValidityCases",
        "local_type_valid",
        "wrongContextValidity",
    ),
    (
        "TypeValidityCases",
        "good_context_wf",
        "wrongContextAdmission",
    ),
    (
        "TypeValidityCases",
        "sort_type_valid",
        "wrongSignatureValidity",
    ),
    ("TypeValidityCases", "empty_wf", "wrongSignatureAdmission"),
    (
        "TypeValidityCases",
        "dependent_application_type_valid",
        "wrongDependentType",
    ),
    ("TypeValidityCases", "local_value_typed", "wrongLookupValue"),
    (
        "TypeValidityCases",
        "dependent_application_scoped",
        "wrongScope",
    ),
    (
        "BinderCongruenceCases",
        "assumption_type_converted",
        "wrongAssumptionType",
    ),
    (
        "BinderCongruenceCases",
        "dependent_pi_congruence",
        "wrongProductBody",
    ),
    (
        "BinderCongruenceCases",
        "dependent_lambda_congruence",
        "wrongLambdaBody",
    ),
    (
        "BinderCongruenceCases",
        "lambda_binder_annotations_ignored",
        "wrongCapturedInner",
    ),
    (
        "BinderCongruenceCases",
        "dependent_lambda_congruence",
        "wrongCommonType",
    ),
    (
        "BinderCongruenceCases",
        "metadata_congruence_preserved",
        "wrongMetadataTerm",
    ),
    ("UniverseConversionCases", "sort_equal", "wrongSort"),
    (
        "UniverseConversionCases",
        "right_endpoint_typed",
        "wrongEndpoint",
    ),
    (
        "UniverseConversionCases",
        "type_transport",
        "wrongTransport",
    ),
    (
        "UniverseConversionCases",
        "equality_transport",
        "wrongEquality",
    ),
    (
        "ApplicationCongruenceCases",
        "family_at_equal_arguments",
        "wrongFamily",
    ),
    (
        "ApplicationCongruenceCases",
        "dependent_term_instantiation",
        "wrongCapturedBody",
    ),
    (
        "ApplicationCongruenceCases",
        "dependent_application",
        "wrongArgument",
    ),
    (
        "ApplicationCongruenceCases",
        "right_application_typed",
        "wrongResultType",
    ),
    (
        "DefinitionConversionCases",
        "local_equality_preserved",
        "wrongUnfolding",
    ),
    (
        "DefinitionConversionCases",
        "converted_local_unfolding",
        "wrongConvertedType",
    ),
    (
        "DefinitionConversionCases",
        "dependent_lambda_preserved",
        "wrongCapturedLambda",
    ),
    (
        "DefinitionConversionCases",
        "nested_definition_preserved",
        "wrongNestedType",
    ),
    (
        "LetCongruenceCases",
        "definition_domain_and_value",
        "wrongLocalType",
    ),
    (
        "LetCongruenceCases",
        "definition_dependent_let",
        "wrongDefinitionBody",
    ),
    (
        "LetCongruenceCases",
        "changed_value_let",
        "wrongChangedValue",
    ),
    (
        "LetCongruenceCases",
        "changed_value_right_typed",
        "wrongResult",
    ),
    (
        "LetCongruenceCases",
        "definition_dependent_changed_value_let",
        "wrongDefinitionDependentBody",
    ),
    (
        "LetCongruenceCases",
        "definition_dependent_changed_value_let",
        "wrongDefinitionDependentValue",
    ),
    (
        "LetCongruenceCases",
        "definition_dependent_changed_value_let",
        "wrongDefinitionDependentType",
    ),
    (
        "LetCongruenceCases",
        "nested_definition_dependent_let",
        "wrongNestedDefinitionBody",
    ),
    (
        "LevelDecideCases",
        "successor_rejected",
        "wrongSuccessorAccepted",
    ),
    (
        "LevelDecideCases",
        "params_rejected",
        "wrongParamsEquivalent",
    ),
    (
        "LevelDecideCases",
        "max_commutes_semantic",
        "wrongSuccessorBound",
    ),
    (
        "LevelDecideCases",
        "imax_successor_semantic",
        "wrongParamEquality",
    ),
    (
        "LevelDecideCases",
        "single_instance_rejects_imax_reflexivity",
        "wrongSingleInstanceAccepts",
    ),
    // Statement non-interchangeability only: `rfl : _ = false` meets `= true`
    // at the literal, whatever `constructorBound` computes. The computed
    // refusal is `constructorBound_sound`'s row in COMPUTATIONAL_CONTROLS.
    (
        "LevelDecideCases",
        "constructor_bound_variable_rejected",
        "wrongConstructorBoundAccepted",
    ),
    ("ListSupportCases", "identity", "wrongIdentity"),
    ("ListSupportCases", "composition", "wrongComposition"),
    ("ListSupportCases", "membership", "wrongMembership"),
    ("ListSupportCases", "length_preserved", "wrongLength"),
    // E6: a control offered at a statement the judgment derives.
    ("NegativeControls", "sort_control", "wrongSortControl"),
    // Constant-safety boundary: forged claim that an unsafe definition is admitted.
    (
        "SafetyBoundary",
        "empty_admitted",
        "wrongUnsafeDefinitionAdmitted",
    ),
];

/// C1's computational controls: `(soundness theorem, relation, accepted pair,
/// rejected pair)`, each in `CICL.Level`. The theorem is applied to
/// `Eq.refl true` at both pairs; the conclusion is the theorem's own. The
/// application is well typed only where the executable test computes `true`,
/// so the accepted pair must be admitted and the rejected one refused with an
/// application type mismatch, by pinned Lean's kernel and by the fenced Clean
/// reference entry. A level is words: the last is `p`, `q` or `zero` (of
/// `CICL.LevelDecideCases` and `CICL.Level`), each one before it `succ`.
pub(super) const COMPUTATIONAL_CONTROLS: &[(&str, &str, [&str; 2], [&str; 2])] = &[
    ("leq_sound", "SemLE", ["p", "succ p"], ["succ p", "p"]),
    ("eqv_sound", "SemEq", ["p", "p"], ["p", "q"]),
    // The rejected pair is `constructor_bound_variable_rejected`'s; its
    // semantic refutation is `CICL.Level.variable_result_refused`.
    (
        "constructorBound_sound",
        "ConstructorBound",
        ["p", "succ p"],
        ["succ zero", "p"],
    ),
];

/// The Lean program that hands each computational control to pinned Lean's
/// kernel and prints the verdict.
pub(super) const LEAN_CONTROL_PROGRAM: &str = "tests/cic_l_level/computational_controls.lean";
