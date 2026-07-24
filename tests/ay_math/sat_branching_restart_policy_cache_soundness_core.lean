-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Checked restart-policy cache soundness skeleton for SAT-COMP SAT solving.
-- Cached branching traces may guide replay only when the policy epoch, seed,
-- trace digest, and learned-clause guard agree with the current run. Any
-- mismatch is a diagnostic no-claim entry that preserves prior public
-- soundness.

def AyPolicyCacheConj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> right -> result) -> result

def AyPolicyCacheDisj (left : Prop) (right : Prop) :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyPolicyCacheEquisat (before : Prop) (after : Prop) :=
  AyPolicyCacheConj (before -> after) (after -> before)

def AyPolicyCacheScope (base : Prop) (assumption : Prop) :=
  forall result : Prop, (base -> assumption -> result) -> result

def AyPolicyCacheState (formula : Prop) (frame : Prop) :=
  AyPolicyCacheConj formula frame

def AyPolicyCacheTrace
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :=
  AyPolicyCacheConj policyEpoch
    (AyPolicyCacheConj seed
      (AyPolicyCacheConj digest
        (AyPolicyCacheConj variableDecision polarityDecision)))

def AyPolicyCacheAgreement
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop) :=
  AyPolicyCacheConj policyEpoch
    (AyPolicyCacheConj seed
      (AyPolicyCacheConj digest
        (AyPolicyCacheConj guard frame)))

def AyPolicyCacheAcceptedReuse
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop) :=
  AyPolicyCacheConj
    (AyPolicyCacheAgreement policyEpoch seed digest guard frame)
    (AyPolicyCacheConj
      (AyPolicyCacheTrace policyEpoch seed digest
        variableDecision polarityDecision)
      (AyPolicyCacheConj learnedClause checker))

def AyPolicyCacheOutcome (model : Prop) (conflict : Prop) :=
  AyPolicyCacheDisj model conflict

def AyPolicyCachePublicReport (outcome : Prop) (frame : Prop) :=
  AyPolicyCacheConj outcome frame

def AyPolicyCacheAcceptedEntry (guidance : Prop) (public : Prop) :=
  AyPolicyCacheConj guidance public

def AyPolicyCacheNoClaimEntry (diagnostic : Prop) (priorPublic : Prop) :=
  AyPolicyCacheConj priorPublic diagnostic

theorem ay_policy_cache_conj_intro
    (left : Prop) (right : Prop) :
    left -> right -> AyPolicyCacheConj left right :=
  fun leftH rightH result build =>
    build leftH rightH

theorem ay_policy_cache_conj_left
    (left : Prop) (right : Prop) :
    AyPolicyCacheConj left right -> left :=
  fun both =>
    both left (fun leftH _rightH => leftH)

theorem ay_policy_cache_conj_right
    (left : Prop) (right : Prop) :
    AyPolicyCacheConj left right -> right :=
  fun both =>
    both right (fun _leftH rightH => rightH)

theorem ay_policy_cache_disj_left
    (left : Prop) (right : Prop) :
    left -> AyPolicyCacheDisj left right :=
  fun leftH result leftCase _rightCase =>
    leftCase leftH

theorem ay_policy_cache_disj_right
    (left : Prop) (right : Prop) :
    right -> AyPolicyCacheDisj left right :=
  fun rightH result _leftCase rightCase =>
    rightCase rightH

theorem ay_policy_cache_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyPolicyCacheEquisat before after :=
  fun forward backward =>
    ay_policy_cache_conj_intro (before -> after) (after -> before)
      forward backward

theorem ay_policy_cache_equisat_forward
    (before : Prop) (after : Prop) :
    AyPolicyCacheEquisat before after -> before -> after :=
  fun equisat =>
    ay_policy_cache_conj_left (before -> after) (after -> before)
      equisat

theorem ay_policy_cache_equisat_backward
    (before : Prop) (after : Prop) :
    AyPolicyCacheEquisat before after -> after -> before :=
  fun equisat =>
    ay_policy_cache_conj_right (before -> after) (after -> before)
      equisat

theorem ay_policy_cache_scope_push
    (base : Prop) (assumption : Prop) :
    base -> assumption -> AyPolicyCacheScope base assumption :=
  fun baseH assumptionH result build =>
    build baseH assumptionH

theorem ay_policy_cache_state_push
    (formula : Prop) (base : Prop) (assumption : Prop) :
    AyPolicyCacheState formula base ->
    assumption ->
    AyPolicyCacheState formula (AyPolicyCacheScope base assumption) :=
  fun state assumptionH =>
    ay_policy_cache_conj_intro formula
      (AyPolicyCacheScope base assumption)
      (ay_policy_cache_conj_left formula base state)
      (ay_policy_cache_scope_push base assumption
        (ay_policy_cache_conj_right formula base state)
        assumptionH)

theorem ay_policy_cache_preprocess_forward
    (original : Prop) (preprocessed : Prop) (frame : Prop) :
    AyPolicyCacheEquisat original preprocessed ->
    AyPolicyCacheState original frame ->
    AyPolicyCacheState preprocessed frame :=
  fun preprocess state =>
    ay_policy_cache_conj_intro preprocessed frame
      (ay_policy_cache_equisat_forward original preprocessed preprocess
        (ay_policy_cache_conj_left original frame state))
      (ay_policy_cache_conj_right original frame state)

theorem ay_policy_cache_trace_intro
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    policyEpoch ->
    seed ->
    digest ->
    variableDecision ->
    polarityDecision ->
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision :=
  fun epochH seedH digestH variableH polarityH =>
    ay_policy_cache_conj_intro policyEpoch
      (AyPolicyCacheConj seed
        (AyPolicyCacheConj digest
          (AyPolicyCacheConj variableDecision polarityDecision)))
      epochH
      (ay_policy_cache_conj_intro seed
        (AyPolicyCacheConj digest
          (AyPolicyCacheConj variableDecision polarityDecision))
        seedH
        (ay_policy_cache_conj_intro digest
          (AyPolicyCacheConj variableDecision polarityDecision)
          digestH
          (ay_policy_cache_conj_intro variableDecision polarityDecision
            variableH polarityH)))

theorem ay_policy_cache_trace_epoch
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision ->
    policyEpoch :=
  fun trace =>
    ay_policy_cache_conj_left policyEpoch
      (AyPolicyCacheConj seed
        (AyPolicyCacheConj digest
          (AyPolicyCacheConj variableDecision polarityDecision)))
      trace

theorem ay_policy_cache_trace_seed
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision ->
    seed :=
  fun trace =>
    ay_policy_cache_conj_left seed
      (AyPolicyCacheConj digest
        (AyPolicyCacheConj variableDecision polarityDecision))
      (ay_policy_cache_conj_right policyEpoch
        (AyPolicyCacheConj seed
          (AyPolicyCacheConj digest
            (AyPolicyCacheConj variableDecision polarityDecision)))
        trace)

theorem ay_policy_cache_trace_digest
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision ->
    digest :=
  fun trace =>
    ay_policy_cache_conj_left digest
      (AyPolicyCacheConj variableDecision polarityDecision)
      (ay_policy_cache_conj_right seed
        (AyPolicyCacheConj digest
          (AyPolicyCacheConj variableDecision polarityDecision))
        (ay_policy_cache_conj_right policyEpoch
          (AyPolicyCacheConj seed
            (AyPolicyCacheConj digest
              (AyPolicyCacheConj variableDecision polarityDecision)))
          trace))

theorem ay_policy_cache_trace_variable
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision ->
    variableDecision :=
  fun trace =>
    ay_policy_cache_conj_left variableDecision polarityDecision
      (ay_policy_cache_conj_right digest
        (AyPolicyCacheConj variableDecision polarityDecision)
        (ay_policy_cache_conj_right seed
          (AyPolicyCacheConj digest
            (AyPolicyCacheConj variableDecision polarityDecision))
          (ay_policy_cache_conj_right policyEpoch
            (AyPolicyCacheConj seed
              (AyPolicyCacheConj digest
                (AyPolicyCacheConj variableDecision polarityDecision)))
            trace)))

theorem ay_policy_cache_trace_polarity
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (variableDecision : Prop) (polarityDecision : Prop) :
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision ->
    polarityDecision :=
  fun trace =>
    ay_policy_cache_conj_right variableDecision polarityDecision
      (ay_policy_cache_conj_right digest
        (AyPolicyCacheConj variableDecision polarityDecision)
        (ay_policy_cache_conj_right seed
          (AyPolicyCacheConj digest
            (AyPolicyCacheConj variableDecision polarityDecision))
          (ay_policy_cache_conj_right policyEpoch
            (AyPolicyCacheConj seed
              (AyPolicyCacheConj digest
                (AyPolicyCacheConj variableDecision polarityDecision)))
            trace)))

theorem ay_policy_cache_agreement_intro
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop) :
    policyEpoch ->
    seed ->
    digest ->
    guard ->
    frame ->
    AyPolicyCacheAgreement policyEpoch seed digest guard frame :=
  fun epochH seedH digestH guardH frameH =>
    ay_policy_cache_conj_intro policyEpoch
      (AyPolicyCacheConj seed
        (AyPolicyCacheConj digest
          (AyPolicyCacheConj guard frame)))
      epochH
      (ay_policy_cache_conj_intro seed
        (AyPolicyCacheConj digest
          (AyPolicyCacheConj guard frame))
        seedH
        (ay_policy_cache_conj_intro digest
          (AyPolicyCacheConj guard frame)
          digestH
          (ay_policy_cache_conj_intro guard frame guardH frameH)))

theorem ay_policy_cache_agreement_epoch
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop) :
    AyPolicyCacheAgreement policyEpoch seed digest guard frame ->
    policyEpoch :=
  fun agreement =>
    ay_policy_cache_conj_left policyEpoch
      (AyPolicyCacheConj seed
        (AyPolicyCacheConj digest
          (AyPolicyCacheConj guard frame)))
      agreement

theorem ay_policy_cache_agreement_seed
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop) :
    AyPolicyCacheAgreement policyEpoch seed digest guard frame ->
    seed :=
  fun agreement =>
    ay_policy_cache_conj_left seed
      (AyPolicyCacheConj digest (AyPolicyCacheConj guard frame))
      (ay_policy_cache_conj_right policyEpoch
        (AyPolicyCacheConj seed
          (AyPolicyCacheConj digest
            (AyPolicyCacheConj guard frame)))
        agreement)

theorem ay_policy_cache_agreement_digest
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop) :
    AyPolicyCacheAgreement policyEpoch seed digest guard frame ->
    digest :=
  fun agreement =>
    ay_policy_cache_conj_left digest
      (AyPolicyCacheConj guard frame)
      (ay_policy_cache_conj_right seed
        (AyPolicyCacheConj digest (AyPolicyCacheConj guard frame))
        (ay_policy_cache_conj_right policyEpoch
          (AyPolicyCacheConj seed
            (AyPolicyCacheConj digest
              (AyPolicyCacheConj guard frame)))
          agreement))

theorem ay_policy_cache_agreement_guard
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop) :
    AyPolicyCacheAgreement policyEpoch seed digest guard frame ->
    guard :=
  fun agreement =>
    ay_policy_cache_conj_left guard frame
      (ay_policy_cache_conj_right digest
        (AyPolicyCacheConj guard frame)
        (ay_policy_cache_conj_right seed
          (AyPolicyCacheConj digest (AyPolicyCacheConj guard frame))
          (ay_policy_cache_conj_right policyEpoch
            (AyPolicyCacheConj seed
              (AyPolicyCacheConj digest
                (AyPolicyCacheConj guard frame)))
            agreement)))

theorem ay_policy_cache_agreement_frame
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop) :
    AyPolicyCacheAgreement policyEpoch seed digest guard frame ->
    frame :=
  fun agreement =>
    ay_policy_cache_conj_right guard frame
      (ay_policy_cache_conj_right digest
        (AyPolicyCacheConj guard frame)
        (ay_policy_cache_conj_right seed
          (AyPolicyCacheConj digest (AyPolicyCacheConj guard frame))
          (ay_policy_cache_conj_right policyEpoch
            (AyPolicyCacheConj seed
              (AyPolicyCacheConj digest
                (AyPolicyCacheConj guard frame)))
            agreement)))

theorem ay_policy_cache_accept_reuse
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPolicyCacheAgreement policyEpoch seed digest guard frame ->
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision ->
    learnedClause ->
    checker ->
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard frame
      variableDecision polarityDecision learnedClause checker :=
  fun agreement trace learnedH checkerH =>
    ay_policy_cache_conj_intro
      (AyPolicyCacheAgreement policyEpoch seed digest guard frame)
      (AyPolicyCacheConj
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCacheConj learnedClause checker))
      agreement
      (ay_policy_cache_conj_intro
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCacheConj learnedClause checker)
        trace
        (ay_policy_cache_conj_intro learnedClause checker
          learnedH checkerH))

theorem ay_policy_cache_reuse_agreement
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard frame
      variableDecision polarityDecision learnedClause checker ->
    AyPolicyCacheAgreement policyEpoch seed digest guard frame :=
  fun reuse =>
    ay_policy_cache_conj_left
      (AyPolicyCacheAgreement policyEpoch seed digest guard frame)
      (AyPolicyCacheConj
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCacheConj learnedClause checker))
      reuse

theorem ay_policy_cache_reuse_trace
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard frame
      variableDecision polarityDecision learnedClause checker ->
    AyPolicyCacheTrace policyEpoch seed digest
      variableDecision polarityDecision :=
  fun reuse =>
    ay_policy_cache_conj_left
      (AyPolicyCacheTrace policyEpoch seed digest
        variableDecision polarityDecision)
      (AyPolicyCacheConj learnedClause checker)
      (ay_policy_cache_conj_right
        (AyPolicyCacheAgreement policyEpoch seed digest guard frame)
        (AyPolicyCacheConj
          (AyPolicyCacheTrace policyEpoch seed digest
            variableDecision polarityDecision)
          (AyPolicyCacheConj learnedClause checker))
        reuse)

theorem ay_policy_cache_reuse_learned_clause
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard frame
      variableDecision polarityDecision learnedClause checker ->
    learnedClause :=
  fun reuse =>
    ay_policy_cache_conj_left learnedClause checker
      (ay_policy_cache_conj_right
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCacheConj learnedClause checker)
        (ay_policy_cache_conj_right
          (AyPolicyCacheAgreement policyEpoch seed digest guard frame)
          (AyPolicyCacheConj
            (AyPolicyCacheTrace policyEpoch seed digest
              variableDecision polarityDecision)
            (AyPolicyCacheConj learnedClause checker))
          reuse))

theorem ay_policy_cache_reuse_checker
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard frame
      variableDecision polarityDecision learnedClause checker ->
    checker :=
  fun reuse =>
    ay_policy_cache_conj_right learnedClause checker
      (ay_policy_cache_conj_right
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCacheConj learnedClause checker)
        (ay_policy_cache_conj_right
          (AyPolicyCacheAgreement policyEpoch seed digest guard frame)
          (AyPolicyCacheConj
            (AyPolicyCacheTrace policyEpoch seed digest
              variableDecision polarityDecision)
            (AyPolicyCacheConj learnedClause checker))
          reuse))

theorem ay_policy_cache_reuse_requires_all_matches
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (frame : Prop)
    (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop) :
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard frame
      variableDecision polarityDecision learnedClause checker ->
    AyPolicyCacheAgreement policyEpoch seed digest guard frame :=
  fun reuse =>
    ay_policy_cache_reuse_agreement policyEpoch seed digest guard frame
      variableDecision polarityDecision learnedClause checker reuse

theorem ay_policy_cache_public_sat_report
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (model conflict : Prop) :
    AyPolicyCacheEquisat original preprocessed ->
    assumption ->
    (preprocessed -> model) ->
    AyPolicyCacheState original base ->
    AyPolicyCachePublicReport
      (AyPolicyCacheOutcome model conflict)
      (AyPolicyCacheScope base assumption) :=
  fun preprocess assumptionH sat state =>
    ay_policy_cache_conj_intro
      (AyPolicyCacheOutcome model conflict)
      (AyPolicyCacheScope base assumption)
      (ay_policy_cache_disj_left model conflict
        (sat
          (ay_policy_cache_conj_left preprocessed
            (AyPolicyCacheScope base assumption)
            (ay_policy_cache_preprocess_forward original preprocessed
              (AyPolicyCacheScope base assumption)
              preprocess
              (ay_policy_cache_state_push original base assumption
                state assumptionH)))))
      (ay_policy_cache_scope_push base assumption
        (ay_policy_cache_conj_right original base state)
        assumptionH)

theorem ay_policy_cache_public_unsat_report
    (base : Prop) (assumption : Prop)
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard
      (AyPolicyCacheScope base assumption)
      variableDecision polarityDecision learnedClause checker ->
    (learnedClause -> conflict) ->
    AyPolicyCachePublicReport
      (AyPolicyCacheOutcome model conflict)
      (AyPolicyCacheScope base assumption) :=
  fun reuse learnedToConflict =>
    ay_policy_cache_conj_intro
      (AyPolicyCacheOutcome model conflict)
      (AyPolicyCacheScope base assumption)
      (ay_policy_cache_disj_right model conflict
        (learnedToConflict
          (ay_policy_cache_reuse_learned_clause policyEpoch seed digest
            guard (AyPolicyCacheScope base assumption)
            variableDecision polarityDecision learnedClause checker reuse)))
      (ay_policy_cache_agreement_frame policyEpoch seed digest guard
        (AyPolicyCacheScope base assumption)
        (ay_policy_cache_reuse_agreement policyEpoch seed digest guard
          (AyPolicyCacheScope base assumption)
          variableDecision polarityDecision learnedClause checker reuse))

theorem ay_policy_cache_accepted_entry_intro
    (guidance : Prop) (public : Prop) :
    guidance -> public -> AyPolicyCacheAcceptedEntry guidance public :=
  fun guidanceH publicH =>
    ay_policy_cache_conj_intro guidance public guidanceH publicH

theorem ay_policy_cache_accepted_entry_guidance
    (guidance : Prop) (public : Prop) :
    AyPolicyCacheAcceptedEntry guidance public -> guidance :=
  fun entry =>
    ay_policy_cache_conj_left guidance public entry

theorem ay_policy_cache_accepted_entry_public
    (guidance : Prop) (public : Prop) :
    AyPolicyCacheAcceptedEntry guidance public -> public :=
  fun entry =>
    ay_policy_cache_conj_right guidance public entry

theorem ay_policy_cache_no_claim_intro
    (diagnostic : Prop) (priorPublic : Prop) :
    priorPublic ->
    diagnostic ->
    AyPolicyCacheNoClaimEntry diagnostic priorPublic :=
  fun priorH diagnosticH =>
    ay_policy_cache_conj_intro priorPublic diagnostic priorH diagnosticH

theorem ay_policy_cache_no_claim_preserves_prior
    (diagnostic : Prop) (priorPublic : Prop) :
    AyPolicyCacheNoClaimEntry diagnostic priorPublic -> priorPublic :=
  fun noClaim =>
    ay_policy_cache_conj_left priorPublic diagnostic noClaim

theorem ay_policy_cache_mismatch_diagnostic
    (epochMismatch : Prop) (seedMismatch : Prop)
    (digestMismatch : Prop) (guardMismatch : Prop)
    (priorPublic : Prop) :
    priorPublic ->
    epochMismatch ->
    seedMismatch ->
    digestMismatch ->
    guardMismatch ->
    AyPolicyCacheNoClaimEntry
      (AyPolicyCacheConj epochMismatch
        (AyPolicyCacheConj
          (AyPolicyCacheConj seedMismatch digestMismatch)
          guardMismatch))
      priorPublic :=
  fun priorH epochH seedH digestH guardH =>
    ay_policy_cache_no_claim_intro
      (AyPolicyCacheConj epochMismatch
        (AyPolicyCacheConj
          (AyPolicyCacheConj seedMismatch digestMismatch)
          guardMismatch))
      priorPublic
      priorH
      (ay_policy_cache_conj_intro epochMismatch
        (AyPolicyCacheConj
          (AyPolicyCacheConj seedMismatch digestMismatch)
          guardMismatch)
        epochH
        (ay_policy_cache_conj_intro
          (AyPolicyCacheConj seedMismatch digestMismatch)
          guardMismatch
          (ay_policy_cache_conj_intro seedMismatch digestMismatch
            seedH digestH)
          guardH))

theorem ay_policy_cache_matching_reuse_guides_sat
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPolicyCacheEquisat original preprocessed ->
    assumption ->
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard
      (AyPolicyCacheScope base assumption)
      variableDecision polarityDecision learnedClause checker ->
    (preprocessed -> model) ->
    AyPolicyCacheState original base ->
    AyPolicyCacheAcceptedEntry
      (AyPolicyCacheTrace policyEpoch seed digest
        variableDecision polarityDecision)
      (AyPolicyCachePublicReport
        (AyPolicyCacheOutcome model conflict)
        (AyPolicyCacheScope base assumption)) :=
  fun preprocess assumptionH reuse sat state =>
    ay_policy_cache_accepted_entry_intro
      (AyPolicyCacheTrace policyEpoch seed digest
        variableDecision polarityDecision)
      (AyPolicyCachePublicReport
        (AyPolicyCacheOutcome model conflict)
        (AyPolicyCacheScope base assumption))
      (ay_policy_cache_reuse_trace policyEpoch seed digest guard
        (AyPolicyCacheScope base assumption)
        variableDecision polarityDecision learnedClause checker reuse)
      (ay_policy_cache_public_sat_report original preprocessed
        base assumption model conflict preprocess assumptionH sat state)

theorem ay_policy_cache_matching_reuse_guides_unsat
    (base : Prop) (assumption : Prop)
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard
      (AyPolicyCacheScope base assumption)
      variableDecision polarityDecision learnedClause checker ->
    (learnedClause -> conflict) ->
    AyPolicyCacheAcceptedEntry
      (AyPolicyCacheTrace policyEpoch seed digest
        variableDecision polarityDecision)
      (AyPolicyCachePublicReport
        (AyPolicyCacheOutcome model conflict)
        (AyPolicyCacheScope base assumption)) :=
  fun reuse learnedToConflict =>
    ay_policy_cache_accepted_entry_intro
      (AyPolicyCacheTrace policyEpoch seed digest
        variableDecision polarityDecision)
      (AyPolicyCachePublicReport
        (AyPolicyCacheOutcome model conflict)
        (AyPolicyCacheScope base assumption))
      (ay_policy_cache_reuse_trace policyEpoch seed digest guard
        (AyPolicyCacheScope base assumption)
        variableDecision polarityDecision learnedClause checker reuse)
      (ay_policy_cache_public_unsat_report base assumption policyEpoch
        seed digest guard variableDecision polarityDecision learnedClause
        checker model conflict reuse learnedToConflict)

theorem ay_policy_cache_full_soundness
    (original : Prop) (preprocessed : Prop)
    (base : Prop) (assumption : Prop)
    (policyEpoch : Prop) (seed : Prop) (digest : Prop)
    (guard : Prop) (variableDecision : Prop) (polarityDecision : Prop)
    (learnedClause : Prop) (checker : Prop)
    (model conflict : Prop) :
    AyPolicyCacheEquisat original preprocessed ->
    assumption ->
    AyPolicyCacheAcceptedReuse policyEpoch seed digest guard
      (AyPolicyCacheScope base assumption)
      variableDecision polarityDecision learnedClause checker ->
    (preprocessed -> model) ->
    (learnedClause -> conflict) ->
    AyPolicyCacheState original base ->
    AyPolicyCacheConj
      (AyPolicyCacheAcceptedEntry
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCachePublicReport
          (AyPolicyCacheOutcome model conflict)
          (AyPolicyCacheScope base assumption)))
      (AyPolicyCacheAcceptedEntry
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCachePublicReport
          (AyPolicyCacheOutcome model conflict)
          (AyPolicyCacheScope base assumption))) :=
  fun preprocess assumptionH reuse sat learnedToConflict state =>
    ay_policy_cache_conj_intro
      (AyPolicyCacheAcceptedEntry
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCachePublicReport
          (AyPolicyCacheOutcome model conflict)
          (AyPolicyCacheScope base assumption)))
      (AyPolicyCacheAcceptedEntry
        (AyPolicyCacheTrace policyEpoch seed digest
          variableDecision polarityDecision)
        (AyPolicyCachePublicReport
          (AyPolicyCacheOutcome model conflict)
          (AyPolicyCacheScope base assumption)))
      (ay_policy_cache_matching_reuse_guides_sat original preprocessed
        base assumption policyEpoch seed digest guard variableDecision
        polarityDecision learnedClause checker model conflict preprocess
        assumptionH reuse sat state)
      (ay_policy_cache_matching_reuse_guides_unsat base assumption
        policyEpoch seed digest guard variableDecision polarityDecision
        learnedClause checker model conflict reuse learnedToConflict)

theorem ay_policy_cache_mismatch_preserves_prior_public_soundness
    (epochMismatch : Prop) (seedMismatch : Prop)
    (digestMismatch : Prop) (guardMismatch : Prop)
    (priorPublic : Prop) :
    AyPolicyCacheNoClaimEntry
      (AyPolicyCacheConj epochMismatch
        (AyPolicyCacheConj
          (AyPolicyCacheConj seedMismatch digestMismatch)
          guardMismatch))
      priorPublic ->
    priorPublic :=
  fun noClaim =>
    ay_policy_cache_no_claim_preserves_prior
      (AyPolicyCacheConj epochMismatch
        (AyPolicyCacheConj
          (AyPolicyCacheConj seedMismatch digestMismatch)
          guardMismatch))
      priorPublic
      noClaim
