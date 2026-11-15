// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plan unit C2 (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`): the
//! design's checker `theories/kcheck_labelled` (labelled terms, token advice,
//! the level report, `kcheck` returning a receipt; design rows 12 and 14 to 18
//! of `designs/2026-11-12-kcheck-model-first.md`, cases of row 21), compiled by
//! pinned Lean over `theories/cic_l`, `theories/cic_l_model` and
//! `theories/kcheck_spec`, replayed by `leanchecker --fresh`, and re-admitted
//! constant by constant through Clean's reference kernel from an empty base.
//!
//! What a green run shows: every constant the package's fifty-seven modules declare
//! is admitted by two kernels; every case line the executable prints
//! (`expected_output.txt`) is stated by a re-admitted theorem `run_<case> =
//! Except.ok ...` or `Except.error ...`, which the kernels decide by evaluating
//! the checker; the axiom closures are the committed ones; the checker's
//! definitions (with the auxiliary constants holding their bodies) and the
//! forged runs' statements have the committed digests; and
//! an accepted run's verdict is admitted at its own statement while each forged
//! run's claimed verdict is refused at its statement (the design's three
//! counter-examples, E6, a forged block, K, the decoder, declaration refusals,
//! a run from `Env.base` in the wrong order, R4-V2's witness, a walk past its
//! stored telescope, D4R4-1's untied index and a stored constructor result too
//! short for the record from the re-check of Revision 4, the two instances of
//! the re-check of Revision 1 and the declarations of R4-V3 and BR4-2 claimed
//! at a lower bound); every advice tag but `MEMO`'s is read by some accepted
//! run, by a re-admitted theorem (`per_token_tags`); and C2's checker, as a
//! `KCheckSpec.Checker`, meets `Checker.StartsAtBase` by a re-admitted
//! theorem (D1 Revision 5). It also re-checks and statement-pins the bounded
//! C3 report-calculus, checker-output and first semantic-base theorems, refuses
//! a dropped-successor report and a proved `Sort 1 : Sort 2` bound at height 1.
//! It qualifies all-fuel soundness of the five checker members, their mutual
//! block, actual ordinary admission and the exact unconditional C3 headline.
//! The actual beta and delta proofs discharge both primitive head laws; the
//! guarded twin and real beta guard-deletion refutation remain checked.
//! This is per-bound semantic soundness against the stated model. It does not
//! show admission of this proof by the adopted checker, compiled-byte lineage,
//! an additional quorum vote or a transfer of authority. The legacy checker
//! `theories/kcheck` is qualified separately by `kcheck_core.rs`.

use std::collections::{BTreeMap, BTreeSet};
use std::process::Command;

use clean_kernel::env::{ConstantInfo, Declaration, Environment};
use clean_kernel::{Expr, ExprKind, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use sha2::{Digest, Sha256};

/// The module that imports every other module of the package.
const ROOT: &str = "KCheck.CheckerContracts";

/// `(accepted case theorem, forged statement)`. Each forged statement is
/// `run_x = v`: an acceptance claimed for a run the checker refuses, or a bound
/// below the one an accepted run returns. The control offers `@Eq.refl T w`
/// for the twin's verdict `w` at the twin's statement, where it is admitted
/// (the reference kernel evaluates the twin's run to `w`), and `@Eq.refl T v`
/// at the forged statement, which is refused only if the kernel evaluates the
/// run to something other than `v`. The twin's own `rfl` (`@rfl T run_twin`)
/// is not offered at the forged statement: there the kernel must first compare
/// two unevaluated runs by lazy delta, which ran out of heartbeats (2 000 000)
/// on the first pair, a refusal that shows no evaluation.
const FORGED_RUNS: &[(&str, &str)] = &[
    ("beta_label_control_accepted", "forged_beta_label"),
    ("telescope_honest_accepted", "forged_telescope_refl"),
    ("telescope_honest_accepted", "forged_telescope_second"),
    ("telescope_honest_accepted", "forged_telescope_reduced"),
    ("const_levels_control_accepted", "forged_const_levels"),
    ("definition_unfolds_accepted", "forged_opaque_delta"),
    ("block_accepted", "forged_block"),
    ("k_accepted", "forged_k_fixture"),
    ("iota_zero_accepted", "forged_k_not_k"),
    ("refl_accepted", "forged_depth_short"),
    ("refl_accepted", "forged_advice_trailing"),
    ("refl_accepted", "forged_memo"),
    ("opaque_accepted", "forged_axiom"),
    ("const_accepted", "forged_not_fresh"),
    ("const_accepted", "forged_theorem_not_prop"),
    ("instance_a_accepted", "forged_instance_a_low"),
    ("instance_b_accepted", "forged_instance_b_low"),
    ("sequence_accepted", "forged_sequence_order"),
    ("telescope_counts_accepted", "forged_telescope_short"),
    ("major_index_control_accepted", "forged_major_index"),
    ("walk_stored_accepted", "forged_walk_past_stored"),
    (
        "result_stored_control_accepted",
        "forged_result_stored_count",
    ),
    ("empty_domain_accepted", "forged_empty_domain_low"),
    ("conv_domain_accepted", "forged_conv_domain_low"),
];

/// The checker's definitions, each pinned by its type and value together with
/// every auxiliary constant Lean declared under its name (`checker_digest`):
/// the decoder and encoder, the level report, the term helpers, the
/// environment helpers, the mutual block, the declaration checker, the run's
/// first handle and the checker as a `KCheckSpec.Checker`. A change
/// to any of them is a deliberate re-pin.
const CHECKER: &[&str] = &[
    "KCheck.readNat",
    "KCheck.decodeAt",
    "KCheck.Advice.start",
    "KCheck.Advice.read",
    "KCheck.Advice.exhausted",
    "KCheck.encodeNat",
    "KCheck.Token.encode",
    "KCheck.encode",
    "KCheck.encodeFrames",
    "KCheck.splitFrames",
    "KCheck.insertOffset",
    "KCheck.reportJoin",
    "KCheck.reportShift",
    "KCheck.reportOfLevel",
    "KCheck.reportAddLevel",
    "KCheck.reportInstantiate",
    "KCheck.reportStart",
    "KCheck.levelSame",
    "KCheck.levelsSame",
    "KCheck.Term.closeAt",
    "KCheck.Term.sameErasure",
    "KCheck.Term.getSpine",
    "KCheck.familyOfRecursor",
    "KCheck.findRule",
    "KCheck.leadingCount",
    "KCheck.recursorArity",
    "KCheck.matchesExpr",
    "KCheck.entryMatches",
    "KCheck.recogniseBlock",
    "KCheck.levelsEqv",
    "KCheck.next",
    "KCheck.lookupLocal",
    "KCheck.findEntry",
    "KCheck.unfoldHead",
    "KCheck.redexAt",
    "KCheck.iotaReduct",
    "KCheck.instR",
    "KCheck.ctorStoredResult",
    "KCheck.ctorResultArgs",
    "KCheck.whnf",
    "KCheck.conv",
    "KCheck.inferAnn",
    "KCheck.check",
    "KCheck.walk",
    "KCheck.levelWithin",
    "KCheck.exprLevelsWithin",
    "KCheck.ordinaryParts",
    "KCheck.checkOrdinary",
    "KCheck.blockName",
    "KCheck.kcheck",
    "KCheck.kcheckBytes",
    "KCheck.base",
    "KCheck.kcheckRun",
    "KCheck.checker",
];

/// C3's proved report-calculus, syntactic output-bound and semantic-base statements. These are
/// theorem statement pins, not checker definition pins; changing one requires
/// an explicit re-check.
const C3_THEOREMS: &[&str] = &[
    "KCheck.reportJoin_eval",
    "KCheck.reportShift_eval",
    "KCheck.level_le_reportOfLevel",
    "KCheck.reportAddLevel_extends",
    "KCheck.level_le_reportAddLevel",
    "KCheck.reportInstantiate_bound",
    "KCheck.reportSuccessor_control",
    "KCheck.whnf_bounded_proved",
    "KCheck.inferAnn_bounded_proved",
    "KCheck.check_bounded_proved",
    "KCheck.report_upper_bound_proved",
    "KCheck.checkSortBound_control",
    "KCheck.WalkSupport.levelSame_eq",
    "KCheck.WalkSupport.levelsSame_eq",
    "KCheck.WalkSupport.sameErasure_toExpr",
    "KCheck.WalkSupport.sameErasure_value",
    "KCheck.WalkSupport.scoped_mono",
    "KCheck.WalkSupport.scoped_inst",
    "KCheck.walk_sound_step",
    "KCheck.walk_sound_of_conv_sound",
    "KCheck.walk_refl_sound_proved",
    "KCheck.walk_argument_typing_control",
    "KCheck.context_depth_transport",
    "KCheck.context_tail_transport",
    "KCheck.context_getElem_semantics",
    "KCheck.lookupLocal_semantics",
    "KCheck.inferAnn_local_sound",
    "KCheck.ContextControls.good_scoped",
    "KCheck.ContextControls.good_satisfies",
    "KCheck.ContextControls.good_lookup_assumption",
    "KCheck.ContextControls.good_lookup_definition",
    "KCheck.ContextControls.lookupLocal_witness",
    "KCheck.ContextControls.bad_satisfies",
    "KCheck.ContextControls.bad_lookup",
    "KCheck.ContextControls.bad_not_scoped",
    "KCheck.ContextControls.bad_not_member",
    "KCheck.ContextControls.lookupLocal_needs_scope",
    "KCheck.BinderSound.scoped_openAt",
    "KCheck.BinderSound.scoped_closeAt",
    "KCheck.BinderSound.closeAt_openAt",
    "KCheck.BinderSound.openAt_closeAt",
    "KCheck.BinderSound.value_openAt",
    "KCheck.BinderSound.ann_openAt",
    "KCheck.BinderSound.value_closeAt",
    "KCheck.BinderSound.ann_closeAt",
    "KCheck.BinderSound.assumptionSetting_exists",
    "KCheck.BinderSound.definitionSetting_exists",
    "KCheck.BinderSound.Controls.body_scoped",
    "KCheck.BinderSound.Controls.body_annotation",
    "KCheck.BinderSound.Controls.body_open_annotation",
    "KCheck.BinderSound.Controls.body_roundtrip",
    "KCheck.BinderSound.Controls.bad_body_annotation",
    "KCheck.BinderSound.Controls.bad_body_not_scoped",
    "KCheck.BinderSound.Controls.bad_body_open_not_annotated",
    "KCheck.BinderSound.Controls.opening_annotation_needs_scope",
    "KCheck.BinderSound.Controls.bad_local_open_value",
    "KCheck.BinderSound.Controls.opening_value_needs_scope",
    "KCheck.BinderSound.closeAt_toExpr",
    "KCheck.BinderSound.empty_in_prop",
    "KCheck.BinderSound.assumptionSetting_nonvacuous",
    "KCheck.BinderSound.prop_in_type",
    "KCheck.BinderSound.definitionSetting_nonvacuous",
    "KCheck.whnfSoundAt_spec",
    "KCheck.inferSoundAt_spec",
    "KCheck.context_getElem_scoped",
    "KCheck.lookupLocal_scoped",
    "KCheck.instLevels_scoped",
    "KCheck.inferAnn_bvar_result",
    "KCheck.inferAnn_local_result",
    "KCheck.inferAnn_sort_result",
    "KCheck.inferAnn_const_result",
    "KCheck.pi_value_mem_sort",
    "KCheck.inferAnn_app_composed",
    "KCheck.inferAnn_lam_composed",
    "KCheck.inferAnn_let_composed",
    "KCheck.inferAnn_pi_composed",
    "KCheck.inferAnn_sound_step",
    "KCheck.inferAnn_sound_of_whnf_conv",
    "KCheck.inferAnn_sound_one",
    "KCheck.InferControls.idProp_run",
    "KCheck.InferControls.idProp_result",
    "KCheck.InferControls.idProp_scoped",
    "KCheck.InferControls.idProp_annotated",
    "KCheck.InferControls.idProp_domain_inhabited",
    "KCheck.InferControls.idProp_witness",
    "KCheck.InferControls.badApp_run",
    "KCheck.InferControls.badApp_scoped",
    "KCheck.InferControls.falseTy_uninhabited",
    "KCheck.InferControls.badApp_not_annotated",
    "KCheck.InferControls.badApp_not_typed",
    "KCheck.InferControls.badApp_control",
    "KCheck.InferControls.inferAnn_needs_annotation",
    "KCheck.ConvModel.traceLambda_congr_on",
    "KCheck.ConvModel.tracePi_congr_on",
    "KCheck.ConvModel.eta_pi",
    "KCheck.ConvModel.proposition_members_related",
    "KCheck.ConvWeakening.semantic_transport",
    "KCheck.ConvWeakening.closed_push",
    "KCheck.convResult_spec",
    "KCheck.ConvLeaves.refl_result",
    "KCheck.ConvLeaves.sort_result",
    "KCheck.ConvLeaves.levelsEqv_eval",
    "KCheck.ConvLeaves.const_result",
    "KCheck.ConvLeaves.app_composed",
    "KCheck.ConvLeaves.irrel_composed",
    "KCheck.conv_lam_composed",
    "KCheck.conv_pi_composed",
    "KCheck.conv_core_left_composed",
    "KCheck.conv_core_right_composed",
    "KCheck.conv_delta_left_composed",
    "KCheck.conv_delta_right_composed",
    "KCheck.conv_delta_both_composed",
    "KCheck.conv_eta_left_composed",
    "KCheck.conv_eta_right_composed",
    "KCheck.conv_sound_step",
    "KCheck.conv_sound_of_whnf_infer_unfold",
    "KCheck.ConvControls.falseTy_value_empty",
    "KCheck.ConvControls.falseTy_member_prop",
    "KCheck.ConvControls.good_beta_run",
    "KCheck.ConvControls.good_beta_scoped",
    "KCheck.ConvControls.falseTy_annotated",
    "KCheck.ConvControls.good_beta_annotated",
    "KCheck.ConvControls.good_beta_related",
    "KCheck.ConvControls.beta_witness",
    "KCheck.ConvControls.bad_beta_run",
    "KCheck.ConvControls.bad_beta_value_empty",
    "KCheck.ConvControls.bad_beta_not_related",
    "KCheck.ConvControls.bad_beta_control",
    "KCheck.ConvControls.conversion_needs_left_annotation",
    "KCheck.ConvControls.scope_lambda_run",
    "KCheck.ConvControls.dangling_lambda_annotated",
    "KCheck.ConvControls.dangling_lambda_not_scoped",
    "KCheck.ConvControls.true_proposition_member",
    "KCheck.ConvControls.scope_lambda_not_related",
    "KCheck.ConvControls.scope_lambda_control",
    "KCheck.ConvControls.conversion_needs_right_scope",
    "KCheck.WhnfSpine.spine_scoped",
    "KCheck.WhnfSpine.spine_ann",
    "KCheck.WhnfSpine.getSpine_reassemble",
    "KCheck.WhnfSpine.getSpine_scoped",
    "KCheck.WhnfSpine.getSpine_ann",
    "KCheck.WhnfSpine.applyN_congr",
    "KCheck.WhnfSpine.spine_congr",
    "KCheck.WhnfSpine.familyOfRecursor_sound",
    "KCheck.WhnfSpine.findRule_sound",
    "KCheck.WhnfShapes.beta_shape",
    "KCheck.WhnfShapes.zeta_shape",
    "KCheck.WhnfShapes.local_shape",
    "KCheck.WhnfShapes.recursor_shape",
    "KCheck.unfoldHead_scoped",
    "KCheck.beta_redex_scoped",
    "KCheck.zeta_redex_scoped",
    "KCheck.zeta_redex_semantics",
    "KCheck.local_redex_scoped",
    "KCheck.local_redex_semantics",
    "KCheck.WhnfFold.bind_ok",
    "KCheck.WhnfFold.report_trans",
    "KCheck.WhnfFold.fold_growth",
    "KCheck.WhnfFold.fold_related",
    "KCheck.WhnfFold.relatedList_refl",
    "KCheck.WhnfFold.relatedList_symm",
    "KCheck.WhnfFold.relatedList_append",
    "KCheck.WhnfRecursor.findEntry_found",
    "KCheck.WhnfRecursor.entry_name",
    "KCheck.WhnfRecursor.const_bound",
    "KCheck.WhnfRecursor.const_type_ann",
    "KCheck.WhnfRecursor.args_scoped_subset",
    "KCheck.WhnfRecursor.args_ann_subset",
    "KCheck.WhnfRecursor.iota_redex_scoped",
    "KCheck.WhnfRecursor.k_redex_scoped",
    "KCheck.WhnfRecursor.rule_rhs_ann",
    "KCheck.WhnfRecursor.rule_rhs_value",
    "KCheck.WhnfLists.prefix_major",
    "KCheck.WhnfLists.recursor_prefix",
    "KCheck.WhnfLists.take_length",
    "KCheck.WhnfLists.index_length",
    "KCheck.WhnfLists.leading_length",
    "KCheck.WhnfLists.k_prefix",
    "KCheck.WhnfK.applyN_append",
    "KCheck.WhnfK.k_redex_semantics",
    "KCheck.whnf_after_head",
    "KCheck.whnf_delta_composed",
    "KCheck.whnf_zeta_composed",
    "KCheck.whnf_local_composed",
    "KCheck.whnf_beta_composed",
    "KCheck.whnf_k_composed",
    "KCheck.WhnfStored.instR_scoped",
    "KCheck.WhnfStored.stored_instR",
    "KCheck.WhnfStored.telescope_residual",
    "KCheck.WhnfStored.spineArgs_scoped",
    "KCheck.WhnfStored.spineArgs_annotated",
    "KCheck.WhnfStored.ctorResultArgs_semantics",
    "KCheck.WhnfStored.inTele_related",
    "KCheck.WhnfIota.applyN_related",
    "KCheck.WhnfIota.iota_redex_semantics",
    "KCheck.whnf_iota_composed",
    "KCheck.whnf_sound_step",
    "KCheck.whnf_sound_of_conv_walk_heads",
    "KCheck.WhnfControls.good_whnf_run",
    "KCheck.WhnfControls.good_whnf_witness",
    "KCheck.WhnfControls.bad_annotation_run",
    "KCheck.WhnfControls.annotation_control",
    "KCheck.WhnfControls.whnf_needs_annotation",
    "KCheck.WhnfControls.bad_scope_run",
    "KCheck.WhnfControls.unscoped_beta_not_scoped",
    "KCheck.WhnfControls.unscoped_beta_annotated",
    "KCheck.WhnfControls.bad_scope_not_related",
    "KCheck.WhnfControls.scope_control",
    "KCheck.WhnfControls.whnf_needs_scope",
    "KCheck.checkSoundAt_spec",
    "KCheck.check_bvar_result",
    "KCheck.check_sort_result",
    "KCheck.check_const_result",
    "KCheck.check_app_composed",
    "KCheck.check_lam_composed",
    "KCheck.check_pi_composed",
    "KCheck.check_let_composed",
    "KCheck.check_sound_step",
    "KCheck.check_sound_of_whnf_conv",
    "KCheck.check_sound_one",
    "KCheck.CheckControls.good_context_scoped",
    "KCheck.CheckControls.good_run",
    "KCheck.CheckControls.good_result",
    "KCheck.CheckControls.good_witness",
    "KCheck.CheckControls.bad_context_run",
    "KCheck.CheckControls.bad_context_not_typed",
    "KCheck.CheckControls.checking_needs_context_scope",
    "KCheck.CheckControls.sort_run",
    "KCheck.CheckControls.sort_result",
    "KCheck.CheckControls.sort_not_self_typed",
    "KCheck.CheckControls.sort_control",
    "KCheck.CheckControls.metadata_run",
    "KCheck.CheckControls.metadata_witness",
    "KCheck.blockSoundAt_spec",
    "KCheck.block_sound_at_zero",
    "KCheck.block_sound_at_step",
    "KCheck.block_sound_at_all_fuel",
    "KCheck.block_sound_of_head_laws",
    "KCheck.whnf_sound_of_head_laws",
    "KCheck.conv_sound_of_head_laws",
    "KCheck.inferAnn_sound_of_head_laws",
    "KCheck.check_sound_of_head_laws",
    "KCheck.walk_sound_of_head_laws",
    "KCheck.EnvTransport.find_old",
    "KCheck.EnvTransport.found_ne_fresh",
    "KCheck.EnvTransport.find_new",
    "KCheck.EnvTransport.find_existing_iff",
    "KCheck.EnvTransport.names_extend",
    "KCheck.EnvTransport.assignment_append",
    "KCheck.EnvTransport.constant_old",
    "KCheck.EnvTransport.constant_new",
    "KCheck.EnvTransport.avoids_fresh",
    "KCheck.EnvTransport.value_same",
    "KCheck.EnvTransport.ann_extend",
    "KCheck.EnvTransport.names_dropPis",
    "KCheck.EnvTransport.names_spineArgs",
    "KCheck.EnvTransport.inTele_iff",
    "KCheck.EnvTransport.mem_ne_fresh",
    "KCheck.EnvTransport.old_entry_valid",
    "KCheck.EnvTransport.old_family_valid",
    "KCheck.EnvTransport.new_entry_valid",
    "KCheck.EnvTransport.append_valid",
    "KCheck.EnvTransport.Controls.identity_evidence",
    "KCheck.EnvTransport.Controls.identity_domain_inhabited",
    "KCheck.EnvTransport.Controls.identity_extension_valid",
    "KCheck.EnvTransport.Controls.identity_base_extension_valid",
    "KCheck.EnvTransport.Controls.identity_punit_family_survives",
    "KCheck.EnvTransport.Controls.nameProbe_scoped",
    "KCheck.EnvTransport.Controls.nameProbe_not_old_named",
    "KCheck.EnvTransport.Controls.probe_fresh",
    "KCheck.EnvTransport.Controls.nameProbe_value_changed",
    "KCheck.EnvTransport.Controls.names_deletion_refuted",
    "KCheck.EnvTransport.Controls.untypedEntry_other_premises",
    "KCheck.EnvTransport.Controls.untypedEntry_not_valid",
    "KCheck.EnvTransport.Controls.typing_deletion_refuted",
    "KCheck.levelSame_sound",
    "KCheck.levelsSame_sound",
    "KCheck.sameErasure_toExpr",
    "KCheck.levelsEqv_eval",
    "KCheck.conv_one_value",
    "KCheck.unfoldHead_sound_proved",
    "KCheck.unfoldHead_scoped_proved",
    "KCheck.unfoldHead_id_control",
    "KCheck.AdmissionShape.levelSame_eq",
    "KCheck.AdmissionShape.levelsSame_eq",
    "KCheck.AdmissionShape.matchesExpr_toExpr",
    "KCheck.AdmissionShape.matchesExpr_sound",
    "KCheck.AdmissionShape.entryMatches_sound",
    "KCheck.AdmissionShape.recogniseBlock_sound",
    "KCheck.AdmissionShape.ordinaryParts_matches",
    "KCheck.ordinary_evidence_from_runs",
    "KCheck.checkOrdinary_sound",
    "KCheck.kcheck_ordinary_sound",
    "KCheck.kcheck_inductive_sound",
    "KCheck.kcheck_quotient_refused",
    "KCheck.kcheck_sound_N_of_block",
    "KCheck.kcheck_sound_of_blocks",
    "KCheck.kcheck_sound_N_of_beta_law",
    "KCheck.kcheck_sound_of_beta_laws",
    "KCheck.c3Owes_of_blocks",
    "KCheck.c3Owes_of_beta_laws",
    "KCheck.AdmissionControls.ordinary_admitted",
    "KCheck.AdmissionControls.admitted_shape",
    "KCheck.AdmissionControls.admitted_fields",
    "KCheck.AdmissionControls.definition_evidence",
    "KCheck.AdmissionControls.admitted_valid",
    "KCheck.AdmissionControls.body_typed_at_old_setting",
    "KCheck.AdmissionControls.admitted_bound_fits",
    "KCheck.AdmissionControls.admission_witness",
    "KCheck.AdmissionControls.admission_bound_control",
    "KCheck.AdmissionControls.theorem_kind_refused",
    "KCheck.AdmissionControls.axiom_refused",
    "KCheck.AdmissionControls.unsafe_refused",
    "KCheck.CompleteSound.beta_head_law",
    "KCheck.CompleteSound.unfold_head_law",
    "KCheck.CompleteSound.block_at_all_fuel",
    "KCheck.CompleteSound.block_sound",
    "KCheck.CompleteSound.whnf_sound",
    "KCheck.CompleteSound.conv_sound",
    "KCheck.CompleteSound.inferAnn_sound",
    "KCheck.CompleteSound.check_sound",
    "KCheck.CompleteSound.walk_sound",
    "KCheck.CompleteSound.kcheck_sound_N",
    "KCheck.CompleteSound.kcheck_sound",
    "KCheck.CompleteSound.c3Owes",
];

/// Independent semantic beta contracts; each actual proof is re-entered at
/// the separately stated contract and refused at False.
const BETA_CONTRACTS: &[(&str, &str)] = &[
    ("KCheck.beta_redex_spine", "betaRedexSpine"),
    ("KCheck.beta_spine_semantics", "betaSpine"),
    ("KCheck.beta_redex_semantics", "betaRedex"),
    ("KCheck.BetaCounterexample.redex", "betaCounterexampleRedex"),
    ("KCheck.BetaCounterexample.term_scoped", "betaInputScoped"),
    ("KCheck.BetaCounterexample.term_bounded", "betaInputBounded"),
    (
        "KCheck.BetaCounterexample.term_annotated",
        "betaInputAnnotated",
    ),
    (
        "KCheck.BetaCounterexample.guarded_beta_control",
        "betaGuardedControl",
    ),
    (
        "KCheck.BetaCounterexample.beta_changes_value",
        "betaCounterexampleUnequal",
    ),
    ("KCheck.beta_needs_label_guard", "betaGuardRequired"),
];

/// The successful generic beta proof must not prove its guard-deleted statement.
const BETA_FORGED: &[(&str, &str)] = &[("KCheck.beta_redex_semantics", "forged_betaWithoutGuard")];

/// Proof-only meanings and concrete witness data, distinct from the executable
/// checker definitions. Their bodies bind the mutation and its real tower.
const BETA_DEFINITIONS: &[&str] = &[
    "KCheck.BetaWithoutLabelGuard",
    "KCheck.BetaCounterexample.term",
    "KCheck.BetaCounterexample.assignment",
    "KCheck.BetaCounterexample.environment",
    "KCheck.BetaCounterexample.guardedTwin",
    "KCheck.BetaContracts.betaWithoutGuard",
];

const FORGED_REPORT: &str = "forged_report_successor";
const FORGED_BOUND: &str = "forged_check_bound_low";

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// The module stems of `theories/kcheck_labelled/ORDER`.
fn order_stems() -> Vec<&'static str> {
    include_str!("../../../theories/kcheck_labelled/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn digest(statement: &Expr) -> String {
    let bytes = bincode::serde::encode_to_vec(statement, bincode::config::standard())
        .expect("serialize a statement");
    hex(&Sha256::digest(&bytes))
}

/// A constant's type and value, in that order, each length-prefixed.
fn feed_constant(hasher: &mut Sha256, constant: &ConstantInfo) {
    for part in std::iter::once(&constant.type_).chain(constant.value.as_ref()) {
        let bytes = bincode::serde::encode_to_vec(part, bincode::config::standard())
            .expect("serialize a checker part");
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
}

/// A checker definition's digest: its type and value, then the name, type and
/// value of each auxiliary constant declared under its name (`<definition>.*`),
/// in name order. Structural recursion puts a body in such a constant: the
/// mutual block's `KCheck.whnf` is a `Nat.brecOn` over `KCheck.whnf._f`, which
/// holds the code, so a digest of `KCheck.whnf` alone misses every change to
/// it (the first run of the re-check of Revision 4's changes moved no pin of
/// the mutual block).
fn checker_digest(constant: &ConstantInfo, auxiliaries: &[(String, &ConstantInfo)]) -> String {
    let mut hasher = Sha256::new();
    feed_constant(&mut hasher, constant);
    for (auxiliary, info) in auxiliaries {
        hasher.update((auxiliary.len() as u64).to_le_bytes());
        hasher.update(auxiliary.as_bytes());
        feed_constant(&mut hasher, info);
    }
    hex(&hasher.finalize())
}

/// `@Eq.refl T v` for the statement `@Eq T lhs v`: a proof whose left side is
/// the claimed verdict itself.
fn verdict_refl(statement: &Expr) -> Expr {
    let ExprKind::Const(head, levels) = statement.get_app_fn().kind() else {
        panic!("a run's statement is an application of Eq: {statement:?}");
    };
    assert_eq!(
        head,
        &name("Eq"),
        "a run's statement is an application of Eq"
    );
    let args = statement.get_app_args();
    assert_eq!(args.len(), 3, "Eq takes a type and two sides");
    Expr::app(
        Expr::app(
            Expr::const_(name("Eq.refl"), levels.clone()),
            (*args[0]).clone(),
        ),
        (*args[2]).clone(),
    )
}

fn is_type_mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}

#[test]
fn kcheck_labelled_rechecks_through_two_kernels_with_forged_runs() {
    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("Lean bin directory");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel one: Lean's own, replaying the root module and everything below
    // it from nothing.
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", ROOT])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .env("PATH", std::env::join_paths(paths).expect("binary path"))
        .output()
        .expect("run pinned independent Lean kernel");
    assert!(
        independent.status.success(),
        "leanchecker --fresh {ROOT} failed: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    // Read actual exported structural names before the expensive import/replay.
    // An imported equation lemma re-exported by a new proof module can share
    // the KCheck namespace, so namespace-prefix checks cannot detect it.
    let mut raw_exports: BTreeMap<Name, String> = BTreeMap::new();
    for stem in order_stems() {
        let module = stem.replace('/', ".");
        let artifact = read_artifact(
            &module,
            &compiled.join(format!("{stem}.olean")),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read raw exports of {module}: {error}"));
        for subject in artifact.names {
            let previous = raw_exports.insert(subject.clone(), module.clone());
            assert!(
                previous.is_none(),
                "duplicate exported structural name {subject}: {previous:?} and {module}"
            );
        }
    }
    eprintln!("raw export preflight: {} distinct names", raw_exports.len());

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load the compiled checker");

    // The subjects are the constants the package's own modules declare, read
    // from each artifact's name table, as in `kcheck_core.rs`: a `CICL.*` or
    // `KCheckSpec.*` constant is never counted as the checker's, and a
    // compiler's `unsafe` copy must be marked so by its own artifact.
    let stems = order_stems();
    assert_eq!(
        stems.len(),
        57,
        "module denominator of theories/kcheck_labelled/ORDER"
    );
    let not_replayable: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut targets: BTreeSet<Name> = BTreeSet::new();
    let mut compiler_copies: BTreeSet<String> = BTreeSet::new();
    for stem in &stems {
        let module = stem.replace('/', ".");
        let artifact = read_artifact(
            &module,
            &compiled.join(format!("{stem}.olean")),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read {module}: {error}"));
        assert!(!artifact.names.is_empty(), "{module} declares nothing");
        let mut copies = 0_usize;
        for constant in &artifact.names {
            let text = constant.to_string();
            if loaded.get_const(constant).is_none() {
                assert!(
                    text.ends_with("._unsafe_rec") && not_replayable.contains(text.as_str()),
                    "{module} declares {constant}, which the load did not make resident and \
                     the artifact does not mark as a compiler's unsafe copy"
                );
                assert!(compiler_copies.insert(text), "{constant} is declared twice");
                copies += 1;
                continue;
            }
            assert!(
                !loaded.is_unsafe(constant) && !loaded.is_partial(constant),
                "{module} declares {constant} unsafe or partial"
            );
            assert!(
                targets.insert(constant.clone()),
                "{constant} is declared by two modules"
            );
        }
        eprintln!(
            "module {module}: {} constants, {copies} unsafe compiler copies",
            artifact.names.len()
        );
    }
    for copy in &compiler_copies {
        let definition = copy
            .strip_suffix("._unsafe_rec")
            .expect("checked when collected");
        assert!(
            targets.contains(&name(definition)),
            "{copy} has no definition among the subjects"
        );
    }

    // Kernel two: Clean's reference kernel, from an empty base. Re-admitting a
    // case theorem evaluates the checker on its run.
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("construct dependency-closed reference replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked
        .into_kernel()
        .expect("all reference admissions passed");

    // Every line the executable prints is a re-admitted theorem's statement:
    // `run_<case> = Except.ok ...` or `Except.error ...`.
    let case_states = |case: &str, accepted: bool| -> bool {
        let suffix = if accepted { "accepted" } else { "refused" };
        let theorem = name(&format!("KCheck.CheckerCases.{case}_{suffix}"));
        let Some(constant) = loaded.get_const(&theorem) else {
            return false;
        };
        let statement = &constant.type_;
        let is_const = |e: &Expr, expected: &str| matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(expected));
        let verdict = if accepted {
            "Except.ok"
        } else {
            "Except.error"
        };
        let run = name(&format!("KCheck.CheckerCases.run_{case}"));
        let mut sides = statement.get_app_args_iter();
        targets.contains(&theorem)
            && targets.contains(&run)
            && constant.value.is_some()
            && is_const(statement, "Eq")
            && statement.get_app_num_args() == 3
            && sides.next().is_some_and(|right| is_const(right, verdict))
            && sides
                .next()
                .is_some_and(|left| matches!(left.kind(), ExprKind::Const(n, _) if n == &run))
    };
    let expected_output = include_str!("../../../theories/kcheck_labelled/expected_output.txt");
    let mut accepted_cases = 0_usize;
    let mut refused_cases = 0_usize;
    let mut summary = None;
    for line in expected_output.lines() {
        if let Some(rest) = line.strip_prefix("cases ") {
            summary = Some(rest.to_owned());
            continue;
        }
        let (case, verdict) = line
            .split_once(": ")
            .unwrap_or_else(|| panic!("malformed verdict line: {line}"));
        let accepted = if verdict.starts_with("accepted ") {
            true
        } else if verdict.starts_with("refused ") {
            false
        } else {
            panic!("verdict line is neither accepted nor refused: {line}");
        };
        assert!(
            case_states(case, accepted),
            "no re-admitted theorem states the verdict of line: {line}"
        );
        if accepted {
            accepted_cases += 1;
        } else {
            refused_cases += 1;
        }
    }
    assert_eq!(
        (accepted_cases, refused_cases),
        (43, 72),
        "exact case denominator"
    );
    assert_eq!(
        summary.as_deref(),
        Some("115, accepted 43, refused 72"),
        "the executable's own count"
    );
    let runs = targets
        .iter()
        .filter(|c| {
            c.to_string()
                .strip_prefix("KCheck.CheckerCases.run_")
                .is_some_and(|case| !case.contains('.'))
        })
        .count();
    assert_eq!(
        runs, 115,
        "every run of KCheck/CheckerCases.lean has an output line"
    );

    // A ground acceptance per token: the advice lists of the per-token
    // acceptances use every tag but `MEMO`'s, by a theorem both kernels
    // admitted (`perTokenTags` is evaluated, not assumed).
    let per_token = name("KCheck.CheckerCases.per_token_tags");
    let coverage = loaded
        .get_const(&per_token)
        .expect("KCheck.CheckerCases.per_token_tags is resident");
    assert!(
        targets.contains(&per_token) && coverage.value.is_some(),
        "KCheck.CheckerCases.per_token_tags is not an admitted theorem of the package"
    );

    // D1 Revision 5 (RT4-1): C2's checker starts at `Env.base`, by a theorem
    // both kernels admitted, stated as `Checker.StartsAtBase KCheck.checker`.
    let starts_at_base = name("KCheck.checker_startsAtBase");
    let starts = loaded
        .get_const(&starts_at_base)
        .expect("KCheck.checker_startsAtBase is resident");
    assert!(
        targets.contains(&starts_at_base) && starts.value.is_some(),
        "KCheck.checker_startsAtBase is not an admitted theorem of the package"
    );
    assert!(
        matches!(starts.type_.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name("KCheckSpec.Checker.StartsAtBase"))
            && starts.type_.get_app_num_args() == 1
            && starts
                .type_
                .get_app_args_iter()
                .next()
                .is_some_and(|checker| matches!(checker.kind(), ExprKind::Const(n, _) if n == &name("KCheck.checker"))),
        "KCheck.checker_startsAtBase does not state Checker.StartsAtBase KCheck.checker"
    );

    // Axiom closures. The checker is computation: no `Classical.choice`.
    let allowed: BTreeSet<String> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let closure_of = |env: &Environment, subject: &Name| -> BTreeSet<String> {
        let mut closure = env.axiom_deps(subject).expect("admitted declaration");
        closure.extend(env.foundational_axiom_deps(subject).expect("closure"));
        closure.iter().map(ToString::to_string).collect()
    };
    let mut union: BTreeSet<String> = BTreeSet::new();
    for subject in &targets {
        let closure = closure_of(kernel.environment(), subject);
        assert!(closure.is_subset(&allowed), "{subject}: {closure:?}");
        union.extend(closure);
    }
    let mut observed_closures: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    observed_closures.insert("*".to_owned(), union);
    for definition in CHECKER.iter().chain(BETA_DEFINITIONS) {
        let subject = name(definition);
        assert!(targets.contains(&subject), "{definition} is not a subject");
        observed_closures.insert(
            (*definition).to_owned(),
            closure_of(kernel.environment(), &subject),
        );
    }
    for theorem in C3_THEOREMS {
        let subject = name(theorem);
        let constant = loaded
            .get_const(&subject)
            .unwrap_or_else(|| panic!("missing C3 theorem {theorem}"));
        assert!(
            targets.contains(&subject) && constant.value.is_some(),
            "{theorem} is not an admitted theorem of the package"
        );
        observed_closures.insert(
            (*theorem).to_owned(),
            closure_of(kernel.environment(), &subject),
        );
    }
    for (theorem, _) in BETA_CONTRACTS {
        let subject = name(theorem);
        assert!(targets.contains(&subject), "missing beta theorem {theorem}");
        observed_closures.insert(
            (*theorem).to_owned(),
            closure_of(kernel.environment(), &subject),
        );
    }
    for (subject, closure) in &observed_closures {
        eprintln!("axiom-closure {subject} {closure:?}");
    }

    // Statement and definition pins. Every digest is printed before any is
    // compared, so one run of a changed set shows all of them.
    let statement = |pin: &str| -> Expr {
        loaded
            .get_const(&name(&format!("KCheck.CheckerContracts.{pin}")))
            .unwrap_or_else(|| panic!("missing statement {pin}"))
            .value
            .clone()
            .unwrap_or_else(|| panic!("{pin} is not a proposition definition"))
    };
    let beta_statement = |pin: &str| -> Expr {
        loaded
            .get_const(&name(&format!("KCheck.BetaContracts.{pin}")))
            .unwrap_or_else(|| panic!("missing beta statement {pin}"))
            .value
            .clone()
            .unwrap_or_else(|| panic!("{pin} is not a proposition definition"))
    };
    let mut observed_pins: BTreeMap<String, String> = BTreeMap::new();
    for (_, pin) in FORGED_RUNS {
        assert!(
            observed_pins
                .insert((*pin).to_owned(), digest(&statement(pin)))
                .is_none(),
            "{pin} is listed twice"
        );
    }
    assert!(
        observed_pins
            .insert(FORGED_REPORT.to_owned(), digest(&statement(FORGED_REPORT)))
            .is_none(),
        "{FORGED_REPORT} is listed twice"
    );
    assert!(
        observed_pins
            .insert(FORGED_BOUND.to_owned(), digest(&statement(FORGED_BOUND)))
            .is_none(),
        "{FORGED_BOUND} is listed twice"
    );
    for theorem in C3_THEOREMS {
        let constant = loaded
            .get_const(&name(theorem))
            .unwrap_or_else(|| panic!("missing C3 theorem {theorem}"));
        assert!(
            observed_pins
                .insert((*theorem).to_owned(), digest(&constant.type_))
                .is_none(),
            "{theorem} is listed twice"
        );
    }
    for (_, pin) in BETA_CONTRACTS.iter().chain(BETA_FORGED) {
        assert!(
            observed_pins
                .insert((*pin).to_owned(), digest(&beta_statement(pin)))
                .is_none(),
            "{pin} is listed twice"
        );
    }
    let mut pinned_auxiliaries: BTreeSet<String> = BTreeSet::new();
    for definition in CHECKER.iter().chain(BETA_DEFINITIONS) {
        let constant = loaded
            .get_const(&name(definition))
            .expect("resident subject");
        assert!(
            constant.value.is_some(),
            "{definition} is pinned as a definition and has no value"
        );
        let prefix = format!("{definition}.");
        let mut auxiliaries: Vec<(String, &ConstantInfo)> = targets
            .iter()
            .filter_map(|subject| {
                let text = subject.to_string();
                text.starts_with(&prefix).then(|| {
                    let info = loaded.get_const(subject).expect("resident subject");
                    (text, info)
                })
            })
            .collect();
        auxiliaries.sort_by(|left, right| left.0.cmp(&right.0));
        eprintln!(
            "checker-pin {definition} auxiliaries [{}]",
            auxiliaries
                .iter()
                .map(|(text, _)| text.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
        pinned_auxiliaries.extend(auxiliaries.iter().map(|(text, _)| text.clone()));
        assert!(
            observed_pins
                .insert(
                    (*definition).to_owned(),
                    checker_digest(constant, &auxiliaries)
                )
                .is_none(),
            "{definition} is listed twice"
        );
    }
    for member in [
        "KCheck.whnf",
        "KCheck.conv",
        "KCheck.inferAnn",
        "KCheck.check",
        "KCheck.walk",
    ] {
        assert!(
            pinned_auxiliaries.contains(&format!("{member}._f")),
            "the body of {member} ({member}._f) is not pinned"
        );
    }
    for (pin, value) in &observed_pins {
        eprintln!("statement-pin {pin} {value}");
    }
    assert_eq!(
        observed_pins.len(),
        FORGED_RUNS.len()
            + 2
            + C3_THEOREMS.len()
            + CHECKER.len()
            + BETA_CONTRACTS.len()
            + BETA_FORGED.len()
            + BETA_DEFINITIONS.len(),
        "pin denominator"
    );
    let committed_closures: BTreeMap<String, BTreeSet<String>> = serde_json::from_str(
        include_str!("../../../theories/kcheck_labelled/axiom_closures.json"),
    )
    .expect("committed axiom closures");
    let committed_pins: BTreeMap<String, String> = serde_json::from_str(include_str!(
        "../../../theories/kcheck_labelled/statement_pins.json"
    ))
    .expect("committed statement pins");
    assert_eq!(
        observed_closures, committed_closures,
        "observed axiom closures differ from theories/kcheck_labelled/axiom_closures.json"
    );
    assert_eq!(
        observed_pins, committed_pins,
        "observed statements differ from theories/kcheck_labelled/statement_pins.json"
    );

    // An accepted run's proof is admitted at its own statement and refused at
    // `False`, and `Eq.refl` of the verdict it states is admitted at it too: the
    // reference kernel evaluates the checker on that run. `Eq.refl` of the
    // verdict the forged run claims, built the same way, is refused at the
    // forged statement by type mismatch: the kernel evaluates the refused run
    // to something else.
    for (case, forged) in FORGED_RUNS {
        let proof = loaded
            .get_const(&name(&format!("KCheck.CheckerCases.{case}")))
            .expect("accepted case");
        let value = proof.value.clone().expect("the case has a proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheck.Controls.{forged}_own_statement")),
                level_params: proof.level_params.clone(),
                type_: proof.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{case} at its own statement: {refusal:?}"));
        let at_false = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{forged}_false")),
            level_params: proof.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&at_false),
            "{case} at False must fail by type mismatch: {at_false:?}"
        );
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheck.Controls.{forged}_twin_verdict")),
                level_params: proof.level_params.clone(),
                type_: proof.type_.clone(),
                value: verdict_refl(&proof.type_),
            })
            .unwrap_or_else(|refusal| {
                panic!("Eq.refl of {case}'s verdict at its own statement: {refusal:?}")
            });
        let forged_statement = statement(forged);
        let claimed = verdict_refl(&forged_statement);
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{forged}")),
            level_params: proof.level_params.clone(),
            type_: forged_statement,
            value: claimed,
        });
        assert!(
            is_type_mismatch(&bad),
            "Eq.refl of {forged}'s claimed verdict must fail by type mismatch: {bad:?}"
        );
    }

    // Each C3 theorem's actual proof re-enters at its pinned statement and
    // is rejected at False. This controls every generic theorem acceptance;
    // the ground mutation below separately exercises executable evaluation.
    for theorem in C3_THEOREMS {
        let constant = loaded
            .get_const(&name(theorem))
            .unwrap_or_else(|| panic!("missing C3 theorem {theorem}"));
        let value = constant
            .value
            .clone()
            .unwrap_or_else(|| panic!("{theorem} has no proof"));
        let control_name = theorem.replace('.', "_");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheck.Controls.{control_name}_own_statement")),
                level_params: constant.level_params.clone(),
                type_: constant.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{theorem} at its own statement: {refusal:?}"));
        let at_false = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{control_name}_false")),
            level_params: constant.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&at_false),
            "{theorem} at False must fail by type mismatch: {at_false:?}"
        );
    }

    // The beta implementation proofs must inhabit independently pinned contracts,
    // not just their own declared types. Each also fails at False, while the
    // guard mutation is positively refuted by betaGuardRequired's theorem.
    for (theorem, pin) in BETA_CONTRACTS {
        let proof = loaded.get_const(&name(theorem)).expect("beta theorem");
        let value = proof.value.clone().expect("beta proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheck.Controls.{pin}_beta_contract")),
                level_params: proof.level_params.clone(),
                type_: beta_statement(pin),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{theorem} at {pin}: {refusal:?}"));
        let at_false = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{pin}_beta_false")),
            level_params: proof.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&at_false),
            "{theorem} at False: {at_false:?}"
        );
    }
    for (theorem, pin) in BETA_FORGED {
        let proof = loaded
            .get_const(&name(theorem))
            .expect("generic beta theorem");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{pin}_beta_forged")),
            level_params: proof.level_params.clone(),
            type_: beta_statement(pin),
            value: proof.value.clone().expect("same actual beta proof"),
        });
        assert!(is_type_mismatch(&bad), "guard deletion must fail: {bad:?}");
    }

    // C3 report-calculus mutation: the proved ground successor report is
    // admitted at its own equation, while both that proof and `Eq.refl` of the
    // forged right-hand side fail at the statement that drops the increment.
    let report_control = loaded
        .get_const(&name("KCheck.reportSuccessor_control"))
        .expect("KCheck.reportSuccessor_control is resident");
    let report_proof = report_control
        .value
        .clone()
        .expect("reportSuccessor_control has a proof");
    kernel
        .add_checked(Declaration::Theorem {
            name: name("KCheck.Controls.report_successor_own_statement"),
            level_params: report_control.level_params.clone(),
            type_: report_control.type_.clone(),
            value: report_proof.clone(),
        })
        .unwrap_or_else(|refusal| panic!("successor report at its own statement: {refusal:?}"));
    let forged_report = statement(FORGED_REPORT);
    let bad_proof = kernel.add_checked(Declaration::Theorem {
        name: name("KCheck.Controls.forged_report_successor_proof"),
        level_params: report_control.level_params.clone(),
        type_: forged_report.clone(),
        value: report_proof,
    });
    assert!(
        is_type_mismatch(&bad_proof),
        "the successor-report proof must fail at the dropped-increment statement: {bad_proof:?}"
    );
    let bad_refl = kernel.add_checked(Declaration::Theorem {
        name: name("KCheck.Controls.forged_report_successor_refl"),
        level_params: report_control.level_params.clone(),
        type_: forged_report.clone(),
        value: verdict_refl(&forged_report),
    });
    assert!(
        is_type_mismatch(&bad_refl),
        "Eq.refl at the dropped-increment statement must fail: {bad_refl:?}"
    );

    // C3 bound mutation: the specialized proof derived through
    // `check_bounded_proved` is valid at height 2 and must fail at the forged
    // height-1 statement, where the returned `Sort 2` is out of bounds.
    let bound_control = loaded
        .get_const(&name("KCheck.checkSortBound_control"))
        .expect("KCheck.checkSortBound_control is resident");
    let bound_proof = bound_control
        .value
        .clone()
        .expect("checkSortBound_control has a proof");
    let forged_bound = statement(FORGED_BOUND);
    let bad_bound = kernel.add_checked(Declaration::Theorem {
        name: name("KCheck.Controls.forged_check_bound_low_proof"),
        level_params: bound_control.level_params.clone(),
        type_: forged_bound,
        value: bound_proof,
    });
    assert!(
        is_type_mismatch(&bad_bound),
        "the height-2 checker-bound proof must fail at height 1: {bad_bound:?}"
    );

    eprintln!(
        "kcheck_labelled subjects {}, modules {}, cases {} ({accepted_cases} accepted, \
         {refused_cases} refused), checker pins {}, C3 theorems {}, forged runs {}, \
         forged C3 controls 2, beta contracts {}, beta guard forgeries {}, beta definition pins {}",
        targets.len(),
        stems.len(),
        accepted_cases + refused_cases,
        CHECKER.len(),
        C3_THEOREMS.len(),
        FORGED_RUNS.len(),
        BETA_CONTRACTS.len(),
        BETA_FORGED.len(),
        BETA_DEFINITIONS.len()
    );
}
