-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked restart-aware deterministic branching trace replay contract. Restart
-- epochs, seed/digest metadata, and branch decisions reproduce guidance only.
-- Public SAT/UNSAT reports remain certificate-derived, while restart, seed,
-- digest, and guard mismatches produce diagnostic no-claim entries.

def AyRestartReplayConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyRestartReplayDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyRestartReplayEquisat (before : Prop) (after : Prop) :=
  AyRestartReplayConj (before -> after) (after -> before)

def AyRestartReplayScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyRestartReplayState (formula : Prop) (frame : Prop) :=
  AyRestartReplayConj formula frame

def AyRestartReplayManifest
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :=
  AyRestartReplayConj epoch
    (AyRestartReplayConj digest
      (AyRestartReplayConj seed
        (AyRestartReplayConj variableDecision polarityDecision)))

def AyRestartReplayAccepted
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :=
  AyRestartReplayConj
    (AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision)
    (AyRestartReplayConj epoch
      (AyRestartReplayConj variableDecision polarityDecision))

def AyRestartReplayGuardMatch (guard : Prop) (frame : Prop) :=
  AyRestartReplayConj guard frame

def AyRestartReplayLearnedEntry
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :=
  AyRestartReplayConj guard
    (AyRestartReplayConj learnedClause checker)

def AyRestartReplayAcceptedReuse
    (frame : Prop) (guard : Prop) (learnedClause : Prop)
    (checker : Prop) :=
  AyRestartReplayConj (AyRestartReplayGuardMatch guard frame)
    (AyRestartReplayLearnedEntry guard learnedClause checker)

def AyRestartReplayOutcome (model : Prop) (conflict : Prop) :=
  AyRestartReplayDisj model conflict

def AyRestartReplayPublicReport (outcome : Prop) (frame : Prop) :=
  AyRestartReplayConj outcome frame

def AyRestartReplayAcceptedEntry (guidance : Prop) (public : Prop) :=
  AyRestartReplayConj guidance public

def AyRestartReplayNoClaimEntry (diagnostic : Prop) (priorLog : Prop) :=
  AyRestartReplayConj priorLog diagnostic

def AyRestartReplayLogAppend (priorLog : Prop) (entry : Prop) :=
  AyRestartReplayConj priorLog entry

theorem ay_restart_replay_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyRestartReplayConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_restart_replay_conj_left
    (left : Prop) (right : Prop) :
    AyRestartReplayConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_restart_replay_conj_right
    (left : Prop) (right : Prop) :
    AyRestartReplayConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_restart_replay_disj_left
    (left : Prop) (right : Prop) :
    left -> AyRestartReplayDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_restart_replay_disj_right
    (left : Prop) (right : Prop) :
    right -> AyRestartReplayDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_restart_replay_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyRestartReplayEquisat before after :=
  fun forward backward =>
    ay_restart_replay_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_restart_replay_equisat_forward
    (before : Prop) (after : Prop) :
    AyRestartReplayEquisat before after -> before -> after :=
  fun equisat =>
    ay_restart_replay_conj_left (before -> after) (after -> before)
      equisat

theorem ay_restart_replay_equisat_backward
    (before : Prop) (after : Prop) :
    AyRestartReplayEquisat before after -> after -> before :=
  fun equisat =>
    ay_restart_replay_conj_right (before -> after) (after -> before)
      equisat

theorem ay_restart_replay_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyRestartReplayScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_restart_replay_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyRestartReplayState formula base ->
    assumption ->
    AyRestartReplayState formula (AyRestartReplayScope base assumption) :=
  fun state assumptionH =>
    ay_restart_replay_conj_intro formula
      (AyRestartReplayScope base assumption)
      (ay_restart_replay_conj_left formula base state)
      (ay_restart_replay_scope_push base assumption
        (ay_restart_replay_conj_right formula base state)
        assumptionH)

theorem ay_restart_replay_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyRestartReplayEquisat original preprocessed ->
    AyRestartReplayState original frame ->
    AyRestartReplayState preprocessed frame :=
  fun preprocess state =>
    ay_restart_replay_conj_intro preprocessed frame
      (ay_restart_replay_equisat_forward original preprocessed preprocess
        (ay_restart_replay_conj_left original frame state))
      (ay_restart_replay_conj_right original frame state)

theorem ay_restart_replay_manifest_intro
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    epoch ->
    digest ->
    seed ->
    variableDecision ->
    polarityDecision ->
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision :=
  fun epochH digestH seedH variableH polarityH =>
    ay_restart_replay_conj_intro epoch
      (AyRestartReplayConj digest
        (AyRestartReplayConj seed
          (AyRestartReplayConj variableDecision polarityDecision)))
      epochH
      (ay_restart_replay_conj_intro digest
        (AyRestartReplayConj seed
          (AyRestartReplayConj variableDecision polarityDecision))
        digestH
        (ay_restart_replay_conj_intro seed
          (AyRestartReplayConj variableDecision polarityDecision)
          seedH
          (ay_restart_replay_conj_intro variableDecision polarityDecision
            variableH polarityH)))

theorem ay_restart_replay_manifest_epoch
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision ->
    epoch :=
  fun manifest =>
    ay_restart_replay_conj_left epoch
      (AyRestartReplayConj digest
        (AyRestartReplayConj seed
          (AyRestartReplayConj variableDecision polarityDecision)))
      manifest

theorem ay_restart_replay_manifest_digest
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision ->
    digest :=
  fun manifest =>
    ay_restart_replay_conj_left digest
      (AyRestartReplayConj seed
        (AyRestartReplayConj variableDecision polarityDecision))
      (ay_restart_replay_conj_right epoch
        (AyRestartReplayConj digest
          (AyRestartReplayConj seed
            (AyRestartReplayConj variableDecision polarityDecision)))
        manifest)

theorem ay_restart_replay_manifest_seed
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision ->
    seed :=
  fun manifest =>
    ay_restart_replay_conj_left seed
      (AyRestartReplayConj variableDecision polarityDecision)
      (ay_restart_replay_conj_right digest
        (AyRestartReplayConj seed
          (AyRestartReplayConj variableDecision polarityDecision))
        (ay_restart_replay_conj_right epoch
          (AyRestartReplayConj digest
            (AyRestartReplayConj seed
              (AyRestartReplayConj variableDecision polarityDecision)))
          manifest))

theorem ay_restart_replay_manifest_variable
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision ->
    variableDecision :=
  fun manifest =>
    ay_restart_replay_conj_left variableDecision polarityDecision
      (ay_restart_replay_conj_right seed
        (AyRestartReplayConj variableDecision polarityDecision)
        (ay_restart_replay_conj_right digest
          (AyRestartReplayConj seed
            (AyRestartReplayConj variableDecision polarityDecision))
          (ay_restart_replay_conj_right epoch
            (AyRestartReplayConj digest
              (AyRestartReplayConj seed
                (AyRestartReplayConj variableDecision polarityDecision)))
            manifest)))

theorem ay_restart_replay_manifest_polarity
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision ->
    polarityDecision :=
  fun manifest =>
    ay_restart_replay_conj_right variableDecision polarityDecision
      (ay_restart_replay_conj_right seed
        (AyRestartReplayConj variableDecision polarityDecision)
        (ay_restart_replay_conj_right digest
          (AyRestartReplayConj seed
            (AyRestartReplayConj variableDecision polarityDecision))
          (ay_restart_replay_conj_right epoch
            (AyRestartReplayConj digest
              (AyRestartReplayConj seed
                (AyRestartReplayConj variableDecision polarityDecision)))
            manifest)))

theorem ay_restart_replay_accept_intro
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision ->
    epoch ->
    variableDecision ->
    polarityDecision ->
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision :=
  fun manifest epochH variableH polarityH =>
    ay_restart_replay_conj_intro
      (AyRestartReplayManifest epoch digest seed variableDecision
        polarityDecision)
      (AyRestartReplayConj epoch
        (AyRestartReplayConj variableDecision polarityDecision))
      manifest
      (ay_restart_replay_conj_intro epoch
        (AyRestartReplayConj variableDecision polarityDecision)
        epochH
        (ay_restart_replay_conj_intro variableDecision polarityDecision
          variableH polarityH))

theorem ay_restart_replay_accepted_manifest
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision :=
  fun replay =>
    ay_restart_replay_conj_left
      (AyRestartReplayManifest epoch digest seed variableDecision
        polarityDecision)
      (AyRestartReplayConj epoch
        (AyRestartReplayConj variableDecision polarityDecision))
      replay

theorem ay_restart_replay_accepted_epoch
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    epoch :=
  fun replay =>
    ay_restart_replay_conj_left epoch
      (AyRestartReplayConj variableDecision polarityDecision)
      (ay_restart_replay_conj_right
        (AyRestartReplayManifest epoch digest seed variableDecision
          polarityDecision)
        (AyRestartReplayConj epoch
          (AyRestartReplayConj variableDecision polarityDecision))
        replay)

theorem ay_restart_replay_accepted_variable
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    variableDecision :=
  fun replay =>
    ay_restart_replay_conj_left variableDecision polarityDecision
      (ay_restart_replay_conj_right epoch
        (AyRestartReplayConj variableDecision polarityDecision)
        (ay_restart_replay_conj_right
          (AyRestartReplayManifest epoch digest seed variableDecision
            polarityDecision)
          (AyRestartReplayConj epoch
            (AyRestartReplayConj variableDecision polarityDecision))
          replay))

theorem ay_restart_replay_accepted_polarity
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    polarityDecision :=
  fun replay =>
    ay_restart_replay_conj_right variableDecision polarityDecision
      (ay_restart_replay_conj_right epoch
        (AyRestartReplayConj variableDecision polarityDecision)
        (ay_restart_replay_conj_right
          (AyRestartReplayManifest epoch digest seed variableDecision
            polarityDecision)
          (AyRestartReplayConj epoch
            (AyRestartReplayConj variableDecision polarityDecision))
          replay))

theorem ay_restart_replay_preserves_decision_guidance
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    AyRestartReplayManifest epoch digest seed variableDecision
      polarityDecision :=
  fun replay =>
    ay_restart_replay_manifest_intro epoch digest seed variableDecision
      polarityDecision
      (ay_restart_replay_accepted_epoch epoch digest seed variableDecision
        polarityDecision replay)
      (ay_restart_replay_manifest_digest epoch digest seed variableDecision
        polarityDecision
        (ay_restart_replay_accepted_manifest epoch digest seed
          variableDecision polarityDecision replay))
      (ay_restart_replay_manifest_seed epoch digest seed variableDecision
        polarityDecision
        (ay_restart_replay_accepted_manifest epoch digest seed
          variableDecision polarityDecision replay))
      (ay_restart_replay_accepted_variable epoch digest seed
        variableDecision polarityDecision replay)
      (ay_restart_replay_accepted_polarity epoch digest seed
        variableDecision polarityDecision replay)

theorem ay_restart_replay_guard_match_intro
    (guard : Prop) (frame : Prop) :
    guard -> frame -> AyRestartReplayGuardMatch guard frame :=
  fun guardH frameH =>
    ay_restart_replay_conj_intro guard frame guardH frameH

theorem ay_restart_replay_guard_match_guard
    (guard : Prop) (frame : Prop) :
    AyRestartReplayGuardMatch guard frame -> guard :=
  fun matched =>
    ay_restart_replay_conj_left guard frame matched

theorem ay_restart_replay_guard_match_frame
    (guard : Prop) (frame : Prop) :
    AyRestartReplayGuardMatch guard frame -> frame :=
  fun matched =>
    ay_restart_replay_conj_right guard frame matched

theorem ay_restart_replay_learned_entry_intro
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    guard ->
    learnedClause ->
    checker ->
    AyRestartReplayLearnedEntry guard learnedClause checker :=
  fun guardH learnedH checkerH =>
    ay_restart_replay_conj_intro guard
      (AyRestartReplayConj learnedClause checker)
      guardH
      (ay_restart_replay_conj_intro learnedClause checker
        learnedH checkerH)

theorem ay_restart_replay_learned_entry_clause
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayLearnedEntry guard learnedClause checker ->
    learnedClause :=
  fun entry =>
    ay_restart_replay_conj_left learnedClause checker
      (ay_restart_replay_conj_right guard
        (AyRestartReplayConj learnedClause checker)
        entry)

theorem ay_restart_replay_learned_entry_checker
    (guard : Prop) (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayLearnedEntry guard learnedClause checker -> checker :=
  fun entry =>
    ay_restart_replay_conj_right learnedClause checker
      (ay_restart_replay_conj_right guard
        (AyRestartReplayConj learnedClause checker)
        entry)

theorem ay_restart_replay_accept_learned_reuse
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayGuardMatch guard frame ->
    AyRestartReplayLearnedEntry guard learnedClause checker ->
    AyRestartReplayAcceptedReuse frame guard learnedClause checker :=
  fun matched entry =>
    ay_restart_replay_conj_intro
      (AyRestartReplayGuardMatch guard frame)
      (AyRestartReplayLearnedEntry guard learnedClause checker)
      matched entry

theorem ay_restart_replay_reuse_guard_match
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayAcceptedReuse frame guard learnedClause checker ->
    AyRestartReplayGuardMatch guard frame :=
  fun reuse =>
    ay_restart_replay_conj_left
      (AyRestartReplayGuardMatch guard frame)
      (AyRestartReplayLearnedEntry guard learnedClause checker)
      reuse

theorem ay_restart_replay_reuse_entry
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayAcceptedReuse frame guard learnedClause checker ->
    AyRestartReplayLearnedEntry guard learnedClause checker :=
  fun reuse =>
    ay_restart_replay_conj_right
      (AyRestartReplayGuardMatch guard frame)
      (AyRestartReplayLearnedEntry guard learnedClause checker)
      reuse

theorem ay_restart_replay_reuse_requires_matching_guard
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayAcceptedReuse frame guard learnedClause checker ->
    guard :=
  fun reuse =>
    ay_restart_replay_guard_match_guard guard frame
      (ay_restart_replay_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_restart_replay_reuse_current_frame
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayAcceptedReuse frame guard learnedClause checker ->
    frame :=
  fun reuse =>
    ay_restart_replay_guard_match_frame guard frame
      (ay_restart_replay_reuse_guard_match frame guard learnedClause
        checker reuse)

theorem ay_restart_replay_reuse_learned_clause
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayAcceptedReuse frame guard learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_restart_replay_learned_entry_clause guard learnedClause checker
      (ay_restart_replay_reuse_entry frame guard learnedClause checker
        reuse)

theorem ay_restart_replay_reuse_checker_artifact
    (frame : Prop) (guard : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyRestartReplayAcceptedReuse frame guard learnedClause checker ->
    checker :=
  fun reuse =>
    ay_restart_replay_learned_entry_checker guard learnedClause checker
      (ay_restart_replay_reuse_entry frame guard learnedClause checker
        reuse)

theorem ay_restart_replay_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyRestartReplayEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyRestartReplayState original base ->
    AyRestartReplayPublicReport
      (AyRestartReplayOutcome model conflict)
      (AyRestartReplayScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_restart_replay_conj_intro
      (AyRestartReplayOutcome model conflict)
      (AyRestartReplayScope base assumption)
      (ay_restart_replay_disj_left model conflict
        (sat
          (ay_restart_replay_conj_left preprocessed
            (AyRestartReplayScope base assumption)
            (ay_restart_replay_preprocess_forward original preprocessed
              (AyRestartReplayScope base assumption)
              preprocess
              (ay_restart_replay_state_push original base assumption
                state assumptionH)))))
      (ay_restart_replay_scope_push base assumption
        (ay_restart_replay_conj_right original base state)
        assumptionH)

theorem ay_restart_replay_public_unsat_report_from_reuse
    (base : Prop) (assumption : Prop)
    (guard : Prop) (learnedClause : Prop)
    (checker : Prop) (model conflict : Prop) :
    AyRestartReplayAcceptedReuse
      (AyRestartReplayScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    AyRestartReplayPublicReport
      (AyRestartReplayOutcome model conflict)
      (AyRestartReplayScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_restart_replay_conj_intro
      (AyRestartReplayOutcome model conflict)
      (AyRestartReplayScope base assumption)
      (ay_restart_replay_disj_right model conflict
        (learnedToConflict
          (ay_restart_replay_reuse_learned_clause
            (AyRestartReplayScope base assumption)
            guard learnedClause checker reuse)))
      (ay_restart_replay_reuse_current_frame
        (AyRestartReplayScope base assumption)
        guard learnedClause checker reuse)

theorem ay_restart_replay_log_append_intro
    (priorLog : Prop) (entry : Prop) :
    priorLog -> entry -> AyRestartReplayLogAppend priorLog entry :=
  fun priorH entryH =>
    ay_restart_replay_conj_intro priorLog entry priorH entryH

theorem ay_restart_replay_log_append_prior
    (priorLog : Prop) (entry : Prop) :
    AyRestartReplayLogAppend priorLog entry -> priorLog :=
  fun appended =>
    ay_restart_replay_conj_left priorLog entry appended

theorem ay_restart_replay_log_append_entry
    (priorLog : Prop) (entry : Prop) :
    AyRestartReplayLogAppend priorLog entry -> entry :=
  fun appended =>
    ay_restart_replay_conj_right priorLog entry appended

theorem ay_restart_replay_accepted_entry_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyRestartReplayAcceptedEntry guidance public :=
  fun guidanceH publicH =>
    ay_restart_replay_conj_intro guidance public guidanceH publicH

theorem ay_restart_replay_accepted_entry_guidance
    (guidance : Prop) (public : Prop) :
    AyRestartReplayAcceptedEntry guidance public -> guidance :=
  fun entry =>
    ay_restart_replay_conj_left guidance public entry

theorem ay_restart_replay_accepted_entry_public
    (guidance : Prop) (public : Prop) :
    AyRestartReplayAcceptedEntry guidance public -> public :=
  fun entry =>
    ay_restart_replay_conj_right guidance public entry

theorem ay_restart_replay_mismatch_no_claim_intro
    (diagnostic : Prop) (priorLog : Prop) :
    priorLog ->
    diagnostic ->
    AyRestartReplayNoClaimEntry diagnostic priorLog :=
  fun priorH diagnosticH =>
    ay_restart_replay_conj_intro priorLog diagnostic priorH diagnosticH

theorem ay_restart_replay_no_claim_preserves_prior
    (diagnostic : Prop) (priorLog : Prop) :
    AyRestartReplayNoClaimEntry diagnostic priorLog -> priorLog :=
  fun noClaim =>
    ay_restart_replay_conj_left priorLog diagnostic noClaim

theorem ay_restart_replay_restart_mismatch_diagnostic
    (restartMismatch : Prop) (priorLog : Prop) :
    priorLog ->
    restartMismatch ->
    AyRestartReplayNoClaimEntry restartMismatch priorLog :=
  fun priorH mismatchH =>
    ay_restart_replay_mismatch_no_claim_intro restartMismatch priorLog
      priorH mismatchH

theorem ay_restart_replay_seed_digest_mismatch_diagnostic
    (seedMismatch : Prop) (digestMismatch : Prop) (priorLog : Prop) :
    priorLog ->
    seedMismatch ->
    digestMismatch ->
    AyRestartReplayNoClaimEntry
      (AyRestartReplayConj seedMismatch digestMismatch)
      priorLog :=
  fun priorH seedH digestH =>
    ay_restart_replay_mismatch_no_claim_intro
      (AyRestartReplayConj seedMismatch digestMismatch)
      priorLog
      priorH
      (ay_restart_replay_conj_intro seedMismatch digestMismatch
        seedH digestH)

theorem ay_restart_replay_guard_mismatch_diagnostic
    (guardMismatch : Prop) (priorLog : Prop) :
    priorLog ->
    guardMismatch ->
    AyRestartReplayNoClaimEntry guardMismatch priorLog :=
  fun priorH mismatchH =>
    ay_restart_replay_mismatch_no_claim_intro guardMismatch priorLog
      priorH mismatchH

theorem ay_restart_replay_accepted_appends_sat_sound_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (model conflict priorLog : Prop) :
    AyRestartReplayEquisat original preprocessed ->
    assumption ->
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    (preprocessed -> model) ->
    AyRestartReplayState original base ->
    priorLog ->
    AyRestartReplayLogAppend priorLog
      (AyRestartReplayAcceptedEntry
        (AyRestartReplayManifest epoch digest seed variableDecision
          polarityDecision)
        (AyRestartReplayPublicReport
          (AyRestartReplayOutcome model conflict)
          (AyRestartReplayScope base assumption))) :=
  fun preprocess assumptionH replay sat state priorH =>
    ay_restart_replay_log_append_intro priorLog
      (AyRestartReplayAcceptedEntry
        (AyRestartReplayManifest epoch digest seed variableDecision
          polarityDecision)
        (AyRestartReplayPublicReport
          (AyRestartReplayOutcome model conflict)
          (AyRestartReplayScope base assumption)))
      priorH
      (ay_restart_replay_accepted_entry_intro
        (AyRestartReplayManifest epoch digest seed variableDecision
          polarityDecision)
        (AyRestartReplayPublicReport
          (AyRestartReplayOutcome model conflict)
          (AyRestartReplayScope base assumption))
        (ay_restart_replay_preserves_decision_guidance
          epoch digest seed variableDecision polarityDecision replay)
        (ay_restart_replay_public_sat_report original preprocessed
          base assumption model conflict preprocess assumptionH sat state))

theorem ay_restart_replay_accepted_appends_unsat_sound_report
    (base : Prop) (assumption : Prop)
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict priorLog : Prop) :
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    AyRestartReplayAcceptedReuse
      (AyRestartReplayScope base assumption)
      guard learnedClause checker ->
    (learnedClause -> conflict) ->
    priorLog ->
    AyRestartReplayLogAppend priorLog
      (AyRestartReplayAcceptedEntry
        (AyRestartReplayManifest epoch digest seed variableDecision
          polarityDecision)
        (AyRestartReplayPublicReport
          (AyRestartReplayOutcome model conflict)
          (AyRestartReplayScope base assumption))) :=
  fun replay reuse learnedToConflict priorH =>
    ay_restart_replay_log_append_intro priorLog
      (AyRestartReplayAcceptedEntry
        (AyRestartReplayManifest epoch digest seed variableDecision
          polarityDecision)
        (AyRestartReplayPublicReport
          (AyRestartReplayOutcome model conflict)
          (AyRestartReplayScope base assumption)))
      priorH
      (ay_restart_replay_accepted_entry_intro
        (AyRestartReplayManifest epoch digest seed variableDecision
          polarityDecision)
        (AyRestartReplayPublicReport
          (AyRestartReplayOutcome model conflict)
          (AyRestartReplayScope base assumption))
        (ay_restart_replay_preserves_decision_guidance
          epoch digest seed variableDecision polarityDecision replay)
        (ay_restart_replay_public_unsat_report_from_reuse
          base assumption guard learnedClause checker model conflict
          reuse learnedToConflict))

theorem ay_restart_replay_matching_epochs_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (epoch : Prop) (digest : Prop) (seed : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (guard : Prop) (learnedClause : Prop) (checker : Prop)
    (model conflict priorLog : Prop) :
    AyRestartReplayEquisat original preprocessed ->
    assumption ->
    AyRestartReplayAccepted epoch digest seed variableDecision
      polarityDecision ->
    AyRestartReplayAcceptedReuse
      (AyRestartReplayScope base assumption)
      guard learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyRestartReplayState original base ->
    priorLog ->
    AyRestartReplayConj
      (AyRestartReplayLogAppend priorLog
        (AyRestartReplayAcceptedEntry
          (AyRestartReplayManifest epoch digest seed variableDecision
            polarityDecision)
          (AyRestartReplayPublicReport
            (AyRestartReplayOutcome model conflict)
            (AyRestartReplayScope base assumption))))
      (AyRestartReplayLogAppend priorLog
        (AyRestartReplayAcceptedEntry
          (AyRestartReplayManifest epoch digest seed variableDecision
            polarityDecision)
          (AyRestartReplayPublicReport
            (AyRestartReplayOutcome model conflict)
            (AyRestartReplayScope base assumption)))) :=
  fun preprocess assumptionH replay reuse sat learnedToConflict
      state priorH =>
    ay_restart_replay_conj_intro
      (AyRestartReplayLogAppend priorLog
        (AyRestartReplayAcceptedEntry
          (AyRestartReplayManifest epoch digest seed variableDecision
            polarityDecision)
          (AyRestartReplayPublicReport
            (AyRestartReplayOutcome model conflict)
            (AyRestartReplayScope base assumption))))
      (AyRestartReplayLogAppend priorLog
        (AyRestartReplayAcceptedEntry
          (AyRestartReplayManifest epoch digest seed variableDecision
            polarityDecision)
          (AyRestartReplayPublicReport
            (AyRestartReplayOutcome model conflict)
            (AyRestartReplayScope base assumption))))
      (ay_restart_replay_accepted_appends_sat_sound_report
        original preprocessed base assumption epoch digest seed
        variableDecision polarityDecision model conflict priorLog
        preprocess assumptionH replay sat state priorH)
      (ay_restart_replay_accepted_appends_unsat_sound_report
        base assumption epoch digest seed variableDecision polarityDecision
        guard learnedClause checker model conflict priorLog replay reuse
        learnedToConflict priorH)

theorem ay_restart_replay_mismatches_append_no_claim
    (restartMismatch : Prop) (seedMismatch : Prop)
    (digestMismatch : Prop) (guardMismatch : Prop)
    (priorLog : Prop) :
    priorLog ->
    restartMismatch ->
    seedMismatch ->
    digestMismatch ->
    guardMismatch ->
    AyRestartReplayLogAppend priorLog
      (AyRestartReplayNoClaimEntry
        (AyRestartReplayConj restartMismatch
          (AyRestartReplayConj
            (AyRestartReplayConj seedMismatch digestMismatch)
            guardMismatch))
        priorLog) :=
  fun priorH restartH seedH digestH guardH =>
    ay_restart_replay_log_append_intro priorLog
      (AyRestartReplayNoClaimEntry
        (AyRestartReplayConj restartMismatch
          (AyRestartReplayConj
            (AyRestartReplayConj seedMismatch digestMismatch)
            guardMismatch))
        priorLog)
      priorH
      (ay_restart_replay_mismatch_no_claim_intro
        (AyRestartReplayConj restartMismatch
          (AyRestartReplayConj
            (AyRestartReplayConj seedMismatch digestMismatch)
            guardMismatch))
        priorLog
        priorH
        (ay_restart_replay_conj_intro restartMismatch
          (AyRestartReplayConj
            (AyRestartReplayConj seedMismatch digestMismatch)
            guardMismatch)
          restartH
          (ay_restart_replay_conj_intro
            (AyRestartReplayConj seedMismatch digestMismatch)
            guardMismatch
            (ay_restart_replay_conj_intro seedMismatch digestMismatch
              seedH digestH)
            guardH)))

theorem ay_restart_replay_mismatch_entries_make_no_public_claim
    (diagnostic : Prop) (priorLog : Prop) :
    AyRestartReplayNoClaimEntry diagnostic priorLog -> priorLog :=
  fun noClaim =>
    ay_restart_replay_no_claim_preserves_prior diagnostic priorLog noClaim
