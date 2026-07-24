-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked audit replay contract for deterministic SAT branching traces. The
-- audit log is append-only metadata: accepted replay entries justify a
-- reproduced run, while seed/digest/guard mismatches are diagnostic no-claim
-- entries. Public SAT/UNSAT soundness remains certificate-derived.

def AyAuditConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyAuditDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyAuditEquisat (before : Prop) (after : Prop) :=
  AyAuditConj (before -> after) (after -> before)

def AyAuditScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyAuditState (formula : Prop) (frame : Prop) :=
  AyAuditConj formula frame

def AyAuditTraceManifest
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :=
  AyAuditConj digest
    (AyAuditConj seed
      (AyAuditConj variableDecision polarityDecision))

def AyAuditReplayAccepted
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :=
  AyAuditConj
    (AyAuditTraceManifest digest seed variableDecision polarityDecision)
    (AyAuditConj variableDecision polarityDecision)

def AyAuditGuardMatch (guard : Prop) (frame : Prop) :=
  AyAuditConj guard frame

def AyAuditLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyAuditConj guard (AyAuditConj learnedClause checker)

def AyAuditAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyAuditConj (AyAuditGuardMatch guard frame)
    (AyAuditLearnedEntry guard learnedClause checker)

def AyAuditOutcome (model : Prop) (conflict : Prop) :=
  AyAuditDisj model conflict

def AyAuditPublicReport (outcome : Prop) (frame : Prop) :=
  AyAuditConj outcome frame

def AyAuditAcceptedEntry (guidance : Prop) (public : Prop) :=
  AyAuditConj guidance public

def AyAuditNoClaimEntry (diagnostic : Prop) (priorLog : Prop) :=
  AyAuditConj priorLog diagnostic

def AyAuditLogAppend (priorLog : Prop) (entry : Prop) :=
  AyAuditConj priorLog entry

theorem ay_audit_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyAuditConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_audit_conj_left
    (left : Prop) (right : Prop) :
    AyAuditConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_audit_conj_right
    (left : Prop) (right : Prop) :
    AyAuditConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_audit_disj_left
    (left : Prop) (right : Prop) :
    left -> AyAuditDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_audit_disj_right
    (left : Prop) (right : Prop) :
    right -> AyAuditDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_audit_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyAuditEquisat before after :=
  fun forward backward =>
    ay_audit_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_audit_equisat_forward
    (before : Prop) (after : Prop) :
    AyAuditEquisat before after -> before -> after :=
  fun equisat =>
    ay_audit_conj_left (before -> after) (after -> before)
      equisat

theorem ay_audit_equisat_backward
    (before : Prop) (after : Prop) :
    AyAuditEquisat before after -> after -> before :=
  fun equisat =>
    ay_audit_conj_right (before -> after) (after -> before)
      equisat

theorem ay_audit_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyAuditScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_audit_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyAuditState formula base ->
    assumption ->
    AyAuditState formula (AyAuditScope base assumption) :=
  fun state assumptionH =>
    ay_audit_conj_intro formula (AyAuditScope base assumption)
      (ay_audit_conj_left formula base state)
      (ay_audit_scope_push base assumption
        (ay_audit_conj_right formula base state)
        assumptionH)

theorem ay_audit_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyAuditEquisat original preprocessed ->
    AyAuditState original frame ->
    AyAuditState preprocessed frame :=
  fun preprocess state =>
    ay_audit_conj_intro preprocessed frame
      (ay_audit_equisat_forward original preprocessed preprocess
        (ay_audit_conj_left original frame state))
      (ay_audit_conj_right original frame state)

theorem ay_audit_trace_manifest_intro
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    digest ->
    seed ->
    variableDecision ->
    polarityDecision ->
    AyAuditTraceManifest digest seed variableDecision polarityDecision :=
  fun digestH seedH variableH polarityH =>
    ay_audit_conj_intro digest
      (AyAuditConj seed
        (AyAuditConj variableDecision polarityDecision))
      digestH
      (ay_audit_conj_intro seed
        (AyAuditConj variableDecision polarityDecision)
        seedH
        (ay_audit_conj_intro variableDecision polarityDecision
          variableH polarityH))

theorem ay_audit_trace_manifest_digest
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditTraceManifest digest seed variableDecision polarityDecision ->
    digest :=
  fun manifest =>
    ay_audit_conj_left digest
      (AyAuditConj seed
        (AyAuditConj variableDecision polarityDecision))
      manifest

theorem ay_audit_trace_manifest_seed
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditTraceManifest digest seed variableDecision polarityDecision ->
    seed :=
  fun manifest =>
    ay_audit_conj_left seed
      (AyAuditConj variableDecision polarityDecision)
      (ay_audit_conj_right digest
        (AyAuditConj seed
          (AyAuditConj variableDecision polarityDecision))
        manifest)

theorem ay_audit_trace_manifest_variable
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditTraceManifest digest seed variableDecision polarityDecision ->
    variableDecision :=
  fun manifest =>
    ay_audit_conj_left variableDecision polarityDecision
      (ay_audit_conj_right seed
        (AyAuditConj variableDecision polarityDecision)
        (ay_audit_conj_right digest
          (AyAuditConj seed
            (AyAuditConj variableDecision polarityDecision))
          manifest))

theorem ay_audit_trace_manifest_polarity
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditTraceManifest digest seed variableDecision polarityDecision ->
    polarityDecision :=
  fun manifest =>
    ay_audit_conj_right variableDecision polarityDecision
      (ay_audit_conj_right seed
        (AyAuditConj variableDecision polarityDecision)
        (ay_audit_conj_right digest
          (AyAuditConj seed
            (AyAuditConj variableDecision polarityDecision))
          manifest))

theorem ay_audit_replay_accept_intro
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditTraceManifest digest seed variableDecision polarityDecision ->
    variableDecision ->
    polarityDecision ->
    AyAuditReplayAccepted digest seed variableDecision polarityDecision :=
  fun manifest variableH polarityH =>
    ay_audit_conj_intro
      (AyAuditTraceManifest digest seed variableDecision polarityDecision)
      (AyAuditConj variableDecision polarityDecision)
      manifest
      (ay_audit_conj_intro variableDecision polarityDecision
        variableH polarityH)

theorem ay_audit_replay_manifest
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditReplayAccepted digest seed variableDecision polarityDecision ->
    AyAuditTraceManifest digest seed variableDecision polarityDecision :=
  fun replay =>
    ay_audit_conj_left
      (AyAuditTraceManifest digest seed variableDecision polarityDecision)
      (AyAuditConj variableDecision polarityDecision)
      replay

theorem ay_audit_replay_variable
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditReplayAccepted digest seed variableDecision polarityDecision ->
    variableDecision :=
  fun replay =>
    ay_audit_conj_left variableDecision polarityDecision
      (ay_audit_conj_right
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditConj variableDecision polarityDecision)
        replay)

theorem ay_audit_replay_polarity
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditReplayAccepted digest seed variableDecision polarityDecision ->
    polarityDecision :=
  fun replay =>
    ay_audit_conj_right variableDecision polarityDecision
      (ay_audit_conj_right
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditConj variableDecision polarityDecision)
        replay)

theorem ay_audit_replay_reproduces_guidance
    (digest : Prop) (seed : Prop) (variableDecision : Prop)
    (polarityDecision : Prop) :
    AyAuditReplayAccepted digest seed variableDecision polarityDecision ->
    AyAuditTraceManifest digest seed variableDecision polarityDecision :=
  fun replay =>
    ay_audit_trace_manifest_intro digest seed variableDecision polarityDecision
      (ay_audit_trace_manifest_digest digest seed variableDecision
        polarityDecision
        (ay_audit_replay_manifest digest seed variableDecision
          polarityDecision replay))
      (ay_audit_trace_manifest_seed digest seed variableDecision
        polarityDecision
        (ay_audit_replay_manifest digest seed variableDecision
          polarityDecision replay))
      (ay_audit_replay_variable digest seed variableDecision
        polarityDecision replay)
      (ay_audit_replay_polarity digest seed variableDecision
        polarityDecision replay)

theorem ay_audit_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyAuditGuardMatch guard frame :=
  fun guardH frameH =>
    ay_audit_conj_intro guard frame guardH frameH

theorem ay_audit_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyAuditGuardMatch guard frame -> guard :=
  fun matched =>
    ay_audit_conj_left guard frame matched

theorem ay_audit_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyAuditGuardMatch guard frame -> frame :=
  fun matched =>
    ay_audit_conj_right guard frame matched

theorem ay_audit_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyAuditLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_audit_conj_intro guard
      (AyAuditConj learnedClause checker)
      guardH
      (ay_audit_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_audit_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyAuditLearnedEntry guard learnedClause checker -> learnedClause :=
  fun entry =>
    ay_audit_conj_left learnedClause checker
      (ay_audit_conj_right guard
        (AyAuditConj learnedClause checker)
        entry)

theorem ay_audit_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyAuditLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_audit_conj_right learnedClause checker
      (ay_audit_conj_right guard
        (AyAuditConj learnedClause checker)
        entry)

theorem ay_audit_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyAuditGuardMatch guard frame ->
    AyAuditLearnedEntry guard learnedClause checker ->
    AyAuditAcceptedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_audit_conj_intro (AyAuditGuardMatch guard frame)
      (AyAuditLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_audit_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyAuditAcceptedReuse frame guard learnedClause checker ->
    AyAuditGuardMatch guard frame :=
  fun reuse =>
    ay_audit_conj_left (AyAuditGuardMatch guard frame)
      (AyAuditLearnedEntry guard learnedClause checker)
      reuse

theorem ay_audit_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyAuditAcceptedReuse frame guard learnedClause checker ->
    AyAuditLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_audit_conj_right (AyAuditGuardMatch guard frame)
      (AyAuditLearnedEntry guard learnedClause checker)
      reuse

theorem ay_audit_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyAuditAcceptedReuse frame guard learnedClause checker -> guard :=
  fun reuse =>
    ay_audit_guard_match_guard guard frame
      (ay_audit_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_audit_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyAuditAcceptedReuse frame guard learnedClause checker -> frame :=
  fun reuse =>
    ay_audit_guard_match_frame guard frame
      (ay_audit_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_audit_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyAuditAcceptedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_audit_learned_entry_clause guard learnedClause checker
      (ay_audit_reuse_entry frame guard learnedClause checker reuse)

theorem ay_audit_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyAuditAcceptedReuse frame guard learnedClause checker -> checker :=
  fun reuse =>
    ay_audit_learned_entry_checker guard learnedClause checker
      (ay_audit_reuse_entry frame guard learnedClause checker reuse)

theorem ay_audit_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyAuditEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyAuditState original base ->
    AyAuditPublicReport
      (AyAuditOutcome model conflict)
      (AyAuditScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_audit_conj_intro
      (AyAuditOutcome model conflict)
      (AyAuditScope base assumption)
      (ay_audit_disj_left model conflict
        (sat
          (ay_audit_conj_left preprocessed
            (AyAuditScope base assumption)
            (ay_audit_preprocess_forward original preprocessed
              (AyAuditScope base assumption)
              preprocess
              (ay_audit_state_push original base assumption
                state assumptionH)))))
      (ay_audit_scope_push base assumption
        (ay_audit_conj_right original base state)
        assumptionH)

theorem ay_audit_public_unsat_report_from_reuse
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyAuditAcceptedReuse
      (AyAuditScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyAuditPublicReport
      (AyAuditOutcome model conflict)
      (AyAuditScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_audit_conj_intro
      (AyAuditOutcome model conflict)
      (AyAuditScope base assumption)
      (ay_audit_disj_right model conflict
        (learnedToConflict
          (ay_audit_reuse_learned_clause
            (AyAuditScope base assumption)
            guard learnedClause checker reuse)))
      (ay_audit_reuse_current_frame
        (AyAuditScope base assumption)
        guard learnedClause checker reuse)

theorem ay_audit_log_append_intro
    (priorLog : Prop) (entry : Prop) :
    priorLog -> entry -> AyAuditLogAppend priorLog entry :=
  fun priorH entryH =>
    ay_audit_conj_intro priorLog entry priorH entryH

theorem ay_audit_log_append_prior
    (priorLog : Prop) (entry : Prop) :
    AyAuditLogAppend priorLog entry -> priorLog :=
  fun appended =>
    ay_audit_conj_left priorLog entry appended

theorem ay_audit_log_append_entry
    (priorLog : Prop) (entry : Prop) :
    AyAuditLogAppend priorLog entry -> entry :=
  fun appended =>
    ay_audit_conj_right priorLog entry appended

theorem ay_audit_accepted_entry_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyAuditAcceptedEntry guidance public :=
  fun guidanceH publicH =>
    ay_audit_conj_intro guidance public guidanceH publicH

theorem ay_audit_accepted_entry_guidance
    (guidance : Prop) (public : Prop) :
    AyAuditAcceptedEntry guidance public -> guidance :=
  fun entry =>
    ay_audit_conj_left guidance public entry

theorem ay_audit_accepted_entry_public
    (guidance : Prop) (public : Prop) :
    AyAuditAcceptedEntry guidance public -> public :=
  fun entry =>
    ay_audit_conj_right guidance public entry

theorem ay_audit_mismatch_no_claim_intro
    (diagnostic : Prop) (priorLog : Prop) :
    priorLog -> diagnostic -> AyAuditNoClaimEntry diagnostic priorLog :=
  fun priorH diagnosticH =>
    ay_audit_conj_intro priorLog diagnostic priorH diagnosticH

theorem ay_audit_mismatch_no_claim_preserves_prior
    (diagnostic : Prop) (priorLog : Prop) :
    AyAuditNoClaimEntry diagnostic priorLog -> priorLog :=
  fun entry =>
    ay_audit_conj_left priorLog diagnostic entry

theorem ay_audit_seed_digest_mismatch_diagnostic
    (seedMismatch : Prop) (digestMismatch : Prop) (priorLog : Prop) :
    priorLog ->
    seedMismatch ->
    digestMismatch ->
    AyAuditNoClaimEntry (AyAuditConj seedMismatch digestMismatch) priorLog :=
  fun priorH seedH digestH =>
    ay_audit_mismatch_no_claim_intro
      (AyAuditConj seedMismatch digestMismatch)
      priorLog
      priorH
      (ay_audit_conj_intro seedMismatch digestMismatch seedH digestH)

theorem ay_audit_guard_mismatch_diagnostic
    (guardMismatch : Prop) (priorLog : Prop) :
    priorLog ->
    guardMismatch ->
    AyAuditNoClaimEntry guardMismatch priorLog :=
  fun priorH mismatchH =>
    ay_audit_mismatch_no_claim_intro guardMismatch priorLog
      priorH mismatchH

theorem ay_audit_accepted_replay_appends_sat_sound_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (model conflict priorLog : Prop) :
    AyAuditEquisat original preprocessed ->
    assumption ->
    AyAuditReplayAccepted digest seed variableDecision polarityDecision ->
    (preprocessed -> model) ->
    AyAuditState original base ->
    priorLog ->
    AyAuditLogAppend priorLog
      (AyAuditAcceptedEntry
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditPublicReport
          (AyAuditOutcome model conflict)
          (AyAuditScope base assumption))) :=
  fun preprocess assumptionH replay sat state priorH =>
    ay_audit_log_append_intro priorLog
      (AyAuditAcceptedEntry
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditPublicReport
          (AyAuditOutcome model conflict)
          (AyAuditScope base assumption)))
      priorH
      (ay_audit_accepted_entry_intro
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditPublicReport
          (AyAuditOutcome model conflict)
          (AyAuditScope base assumption))
        (ay_audit_replay_reproduces_guidance
          digest seed variableDecision polarityDecision replay)
        (ay_audit_public_sat_report original preprocessed base assumption
          model conflict preprocess assumptionH sat state))

theorem ay_audit_accepted_replay_appends_unsat_sound_report
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict priorLog : Prop) :
    AyAuditReplayAccepted digest seed variableDecision polarityDecision ->
    AyAuditAcceptedReuse
      (AyAuditScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    priorLog ->
    AyAuditLogAppend priorLog
      (AyAuditAcceptedEntry
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditPublicReport
          (AyAuditOutcome model conflict)
          (AyAuditScope base assumption))) :=
  fun replay reuse learnedToConflict priorH =>
    ay_audit_log_append_intro priorLog
      (AyAuditAcceptedEntry
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditPublicReport
          (AyAuditOutcome model conflict)
          (AyAuditScope base assumption)))
      priorH
      (ay_audit_accepted_entry_intro
        (AyAuditTraceManifest digest seed variableDecision polarityDecision)
        (AyAuditPublicReport
          (AyAuditOutcome model conflict)
          (AyAuditScope base assumption))
        (ay_audit_replay_reproduces_guidance
          digest seed variableDecision polarityDecision replay)
        (ay_audit_public_unsat_report_from_reuse
          base assumption guard learnedClause checker model conflict
          reuse learnedToConflict))

theorem ay_audit_accepted_replay_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict priorLog : Prop) :
    AyAuditEquisat original preprocessed ->
    assumption ->
    AyAuditReplayAccepted digest seed variableDecision polarityDecision ->
    AyAuditAcceptedReuse
      (AyAuditScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyAuditState original base ->
    priorLog ->
    AyAuditConj
      (AyAuditLogAppend priorLog
        (AyAuditAcceptedEntry
          (AyAuditTraceManifest digest seed variableDecision polarityDecision)
          (AyAuditPublicReport
            (AyAuditOutcome model conflict)
            (AyAuditScope base assumption))))
      (AyAuditLogAppend priorLog
        (AyAuditAcceptedEntry
          (AyAuditTraceManifest digest seed variableDecision polarityDecision)
          (AyAuditPublicReport
            (AyAuditOutcome model conflict)
            (AyAuditScope base assumption)))) :=
  fun preprocess assumptionH replay reuse sat learnedToConflict state priorH =>
    ay_audit_conj_intro
      (AyAuditLogAppend priorLog
        (AyAuditAcceptedEntry
          (AyAuditTraceManifest digest seed variableDecision polarityDecision)
          (AyAuditPublicReport
            (AyAuditOutcome model conflict)
            (AyAuditScope base assumption))))
      (AyAuditLogAppend priorLog
        (AyAuditAcceptedEntry
          (AyAuditTraceManifest digest seed variableDecision polarityDecision)
          (AyAuditPublicReport
            (AyAuditOutcome model conflict)
            (AyAuditScope base assumption))))
      (ay_audit_accepted_replay_appends_sat_sound_report
        original preprocessed base assumption digest seed variableDecision
        polarityDecision model conflict priorLog preprocess assumptionH
        replay sat state priorH)
      (ay_audit_accepted_replay_appends_unsat_sound_report
        base assumption digest seed variableDecision polarityDecision
        guard learnedClause checker model conflict priorLog replay reuse
        learnedToConflict priorH)

theorem ay_audit_mismatch_appends_no_claim
    (seedMismatch : Prop) (digestMismatch : Prop)
    (guardMismatch : Prop) (priorLog : Prop) :
    priorLog ->
    seedMismatch ->
    digestMismatch ->
    guardMismatch ->
    AyAuditLogAppend priorLog
      (AyAuditNoClaimEntry
        (AyAuditConj (AyAuditConj seedMismatch digestMismatch)
          guardMismatch)
        priorLog) :=
  fun priorH seedH digestH guardH =>
    ay_audit_log_append_intro priorLog
      (AyAuditNoClaimEntry
        (AyAuditConj (AyAuditConj seedMismatch digestMismatch)
          guardMismatch)
        priorLog)
      priorH
      (ay_audit_mismatch_no_claim_intro
        (AyAuditConj (AyAuditConj seedMismatch digestMismatch)
          guardMismatch)
        priorLog
        priorH
        (ay_audit_conj_intro
          (AyAuditConj seedMismatch digestMismatch)
          guardMismatch
          (ay_audit_conj_intro seedMismatch digestMismatch seedH digestH)
          guardH))

theorem ay_audit_mismatch_entries_make_no_public_claim
    (diagnostic : Prop) (priorLog : Prop) :
    AyAuditNoClaimEntry diagnostic priorLog -> priorLog :=
  fun noClaim =>
    ay_audit_mismatch_no_claim_preserves_prior diagnostic priorLog noClaim
