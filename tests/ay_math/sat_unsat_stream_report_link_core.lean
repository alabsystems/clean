-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0

-- Validator-report linkage for UNSAT stream manifest/cache results. The report
-- exposes original UNSAT only when a retained manifest-linked stream proof or a
-- direct recheck proof is accepted; unavailable cache states remain no-claim.

def AyUSRLConj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> q -> result) -> result

def AyUSRLDisj (p : Prop) (q : Prop) :=
  forall result : Prop, (p -> result) -> (q -> result) -> result

def AyUSRLMap (source : Prop) (target : Prop) :=
  source -> target

def AyUSRLEquisat (before : Prop) (after : Prop) :=
  AyUSRLConj (before -> after) (after -> before)

def AyUSRLAuditEnvelope
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop) :=
  AyUSRLConj validatorExitCode
    (AyUSRLConj auditDigest acceptedReport)

def AyUSRLRetainedStreamProof
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSRLConj visibleChunk
    (AyUSRLConj
      (AyUSRLMap visibleChunk checkpointSnapshot)
      (AyUSRLConj
        (AyUSRLMap checkpointSnapshot finalAccumulator)
        (AyUSRLConj
          (AyUSRLMap finalAccumulator emptyClause)
          (AyUSRLConj
            (AyUSRLMap emptyClause visibleUnsat)
            (AyUSRLMap visibleUnsat originalUnsat)))))

def AyUSRLDirectRecheckProof
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSRLRetainedStreamProof visibleChunk checkpointSnapshot finalAccumulator
    emptyClause visibleUnsat originalUnsat

def AyUSRLUnavailableNoClaim
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) :=
  AyUSRLConj fallbackNoClaim
    (AyUSRLDisj missingEntry evictedEntry)

def AyUSRLReportOutcome
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :=
  AyUSRLDisj fallbackNoClaim originalUnsat

def AyUSRLValidatorReport
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :=
  AyUSRLConj
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLReportOutcome fallbackNoClaim originalUnsat)

def AyUSRLRetainedReportContract
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSRLConj
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLRetainedStreamProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat)

def AyUSRLDirectReportContract
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :=
  AyUSRLConj
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLDirectRecheckProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat)

def AyUSRLUnavailableReportContract
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) :=
  AyUSRLConj
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLUnavailableNoClaim missingEntry evictedEntry fallbackNoClaim)

theorem ay_usrl_conj_intro
    (p : Prop) (q : Prop) :
    p -> q -> AyUSRLConj p q := by
  intro hp
  intro hq
  intro result
  intro build
  exact build hp hq

theorem ay_usrl_conj_left
    (p : Prop) (q : Prop) :
    AyUSRLConj p q -> p := by
  intro both
  exact both p (fun hp _hq => hp)

theorem ay_usrl_disj_left
    (p : Prop) (q : Prop) :
    p -> AyUSRLDisj p q := by
  intro hp
  intro result
  intro left_to_result
  intro _right_to_result
  exact left_to_result hp

theorem ay_usrl_disj_right
    (p : Prop) (q : Prop) :
    q -> AyUSRLDisj p q := by
  intro hq
  intro result
  intro _left_to_result
  intro right_to_result
  exact right_to_result hq

theorem ay_usrl_equisat_intro
    (before : Prop) (after : Prop) :
    (before -> after) ->
    (after -> before) ->
    AyUSRLEquisat before after := by
  intro forward
  intro backward
  exact ay_usrl_conj_intro
    (before -> after)
    (after -> before)
    forward
    backward

theorem ay_usrl_audit_exit_code
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop) :
    AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport ->
    validatorExitCode := by
  intro envelope
  exact ay_usrl_conj_left validatorExitCode
    (AyUSRLConj auditDigest acceptedReport)
    envelope

theorem ay_usrl_audit_digest
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop) :
    AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport ->
    auditDigest := by
  intro envelope
  exact envelope auditDigest
    (fun _exit tail =>
      tail auditDigest
        (fun digest _accepted => digest))

theorem ay_usrl_audit_accepted
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop) :
    AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport ->
    acceptedReport := by
  intro envelope
  exact envelope acceptedReport
    (fun _exit tail =>
      tail acceptedReport
        (fun _digest accepted => accepted))

theorem ay_usrl_stream_final_accumulator
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSRLRetainedStreamProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    finalAccumulator := by
  intro proof
  exact proof finalAccumulator
    (fun hvisible tail =>
      tail finalAccumulator
        (fun visible_to_checkpoint tail2 =>
          tail2 finalAccumulator
            (fun checkpoint_to_final _tail3 =>
              checkpoint_to_final (visible_to_checkpoint hvisible))))

theorem ay_usrl_stream_original_unsat
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSRLRetainedStreamProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro proof
  exact proof originalUnsat
    (fun hvisible tail =>
      tail originalUnsat
        (fun visible_to_checkpoint tail2 =>
          tail2 originalUnsat
            (fun checkpoint_to_final tail3 =>
              tail3 originalUnsat
                (fun final_to_empty tail4 =>
                  tail4 originalUnsat
                    (fun empty_to_unsat unsat_to_original =>
                      unsat_to_original
                        (empty_to_unsat
                          (final_to_empty
                            (checkpoint_to_final
                              (visible_to_checkpoint hvisible)))))))))))

theorem ay_usrl_direct_original_unsat
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSRLDirectRecheckProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat ->
    originalUnsat := by
  intro proof
  exact ay_usrl_stream_original_unsat
    visibleChunk checkpointSnapshot finalAccumulator emptyClause
    visibleUnsat originalUnsat proof

theorem ay_usrl_report_outcome_unsat
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    originalUnsat ->
    AyUSRLReportOutcome fallbackNoClaim originalUnsat := by
  intro unsat
  exact ay_usrl_disj_right fallbackNoClaim originalUnsat unsat

theorem ay_usrl_report_outcome_no_claim
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    fallbackNoClaim ->
    AyUSRLReportOutcome fallbackNoClaim originalUnsat := by
  intro no_claim
  exact ay_usrl_disj_left fallbackNoClaim originalUnsat no_claim

theorem ay_usrl_validator_report_intro
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport ->
    AyUSRLReportOutcome fallbackNoClaim originalUnsat ->
    AyUSRLValidatorReport validatorExitCode auditDigest acceptedReport
      fallbackNoClaim originalUnsat := by
  intro envelope
  intro outcome
  exact ay_usrl_conj_intro
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLReportOutcome fallbackNoClaim originalUnsat)
    envelope
    outcome

theorem ay_usrl_retained_contract_envelope
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSRLRetainedReportContract validatorExitCode auditDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport := by
  intro contract
  exact ay_usrl_conj_left
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLRetainedStreamProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat)
    contract

theorem ay_usrl_retained_contract_proof
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSRLRetainedReportContract validatorExitCode auditDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSRLRetainedStreamProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUSRLRetainedStreamProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat)
    (fun _envelope proof => proof)

theorem ay_usrl_direct_contract_envelope
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSRLDirectReportContract validatorExitCode auditDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport := by
  intro contract
  exact ay_usrl_conj_left
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLDirectRecheckProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat)
    contract

theorem ay_usrl_direct_contract_proof
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop) :
    AyUSRLDirectReportContract validatorExitCode auditDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSRLDirectRecheckProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat := by
  intro contract
  exact contract
    (AyUSRLDirectRecheckProof visibleChunk checkpointSnapshot
      finalAccumulator emptyClause visibleUnsat originalUnsat)
    (fun _envelope proof => proof)

theorem ay_usrl_retained_report_exposes_unsat
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (fallbackNoClaim : Prop) :
    AyUSRLRetainedReportContract validatorExitCode auditDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSRLValidatorReport validatorExitCode auditDigest acceptedReport
      fallbackNoClaim originalUnsat := by
  intro contract
  exact ay_usrl_validator_report_intro
    validatorExitCode auditDigest acceptedReport fallbackNoClaim originalUnsat
    (ay_usrl_retained_contract_envelope
      validatorExitCode auditDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat contract)
    (ay_usrl_report_outcome_unsat fallbackNoClaim originalUnsat
      (ay_usrl_stream_original_unsat
        visibleChunk checkpointSnapshot finalAccumulator emptyClause
        visibleUnsat originalUnsat
        (ay_usrl_retained_contract_proof
          validatorExitCode auditDigest acceptedReport visibleChunk
          checkpointSnapshot finalAccumulator emptyClause visibleUnsat
          originalUnsat contract)))

theorem ay_usrl_direct_report_exposes_unsat
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (visibleChunk : Prop) (checkpointSnapshot : Prop)
    (finalAccumulator : Prop) (emptyClause : Prop)
    (visibleUnsat : Prop) (originalUnsat : Prop)
    (fallbackNoClaim : Prop) :
    AyUSRLDirectReportContract validatorExitCode auditDigest acceptedReport
      visibleChunk checkpointSnapshot finalAccumulator emptyClause
      visibleUnsat originalUnsat ->
    AyUSRLValidatorReport validatorExitCode auditDigest acceptedReport
      fallbackNoClaim originalUnsat := by
  intro contract
  exact ay_usrl_validator_report_intro
    validatorExitCode auditDigest acceptedReport fallbackNoClaim originalUnsat
    (ay_usrl_direct_contract_envelope
      validatorExitCode auditDigest acceptedReport visibleChunk
      checkpointSnapshot finalAccumulator emptyClause visibleUnsat
      originalUnsat contract)
    (ay_usrl_report_outcome_unsat fallbackNoClaim originalUnsat
      (ay_usrl_direct_original_unsat
        visibleChunk checkpointSnapshot finalAccumulator emptyClause
        visibleUnsat originalUnsat
        (ay_usrl_direct_contract_proof
          validatorExitCode auditDigest acceptedReport visibleChunk
          checkpointSnapshot finalAccumulator emptyClause visibleUnsat
          originalUnsat contract)))

theorem ay_usrl_unavailable_no_claim
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) :
    AyUSRLUnavailableNoClaim
      missingEntry evictedEntry fallbackNoClaim ->
    fallbackNoClaim := by
  intro unavailable
  exact ay_usrl_conj_left fallbackNoClaim
    (AyUSRLDisj missingEntry evictedEntry)
    unavailable

theorem ay_usrl_unavailable_contract_envelope
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) :
    AyUSRLUnavailableReportContract validatorExitCode auditDigest
      acceptedReport missingEntry evictedEntry fallbackNoClaim ->
    AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport := by
  intro contract
  exact ay_usrl_conj_left
    (AyUSRLAuditEnvelope validatorExitCode auditDigest acceptedReport)
    (AyUSRLUnavailableNoClaim missingEntry evictedEntry fallbackNoClaim)
    contract

theorem ay_usrl_unavailable_contract_state
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) :
    AyUSRLUnavailableReportContract validatorExitCode auditDigest
      acceptedReport missingEntry evictedEntry fallbackNoClaim ->
    AyUSRLUnavailableNoClaim missingEntry evictedEntry fallbackNoClaim := by
  intro contract
  exact contract
    (AyUSRLUnavailableNoClaim missingEntry evictedEntry fallbackNoClaim)
    (fun _envelope unavailable => unavailable)

theorem ay_usrl_unavailable_report_no_claim
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    AyUSRLUnavailableReportContract validatorExitCode auditDigest
      acceptedReport missingEntry evictedEntry fallbackNoClaim ->
    AyUSRLValidatorReport validatorExitCode auditDigest acceptedReport
      fallbackNoClaim originalUnsat := by
  intro contract
  exact ay_usrl_validator_report_intro
    validatorExitCode auditDigest acceptedReport fallbackNoClaim originalUnsat
    (ay_usrl_unavailable_contract_envelope
      validatorExitCode auditDigest acceptedReport missingEntry evictedEntry
      fallbackNoClaim contract)
    (ay_usrl_report_outcome_no_claim fallbackNoClaim originalUnsat
      (ay_usrl_unavailable_no_claim missingEntry evictedEntry fallbackNoClaim
        (ay_usrl_unavailable_contract_state
          validatorExitCode auditDigest acceptedReport missingEntry evictedEntry
          fallbackNoClaim contract)))

theorem ay_usrl_report_unsat_only_when_accepted
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    AyUSRLValidatorReport validatorExitCode auditDigest acceptedReport
      fallbackNoClaim originalUnsat ->
    (fallbackNoClaim -> originalUnsat -> False) ->
    originalUnsat ->
    acceptedReport := by
  intro report
  intro _no_claim_blocks_unsat
  intro _unsat
  exact report acceptedReport
    (fun envelope _outcome =>
      ay_usrl_audit_accepted
        validatorExitCode auditDigest acceptedReport envelope)

theorem ay_usrl_unavailable_remains_no_claim
    (validatorExitCode : Prop) (auditDigest : Prop)
    (acceptedReport : Prop)
    (missingEntry : Prop) (evictedEntry : Prop)
    (fallbackNoClaim : Prop) (originalUnsat : Prop) :
    AyUSRLUnavailableReportContract validatorExitCode auditDigest
      acceptedReport missingEntry evictedEntry fallbackNoClaim ->
    (fallbackNoClaim -> originalUnsat -> False) ->
    originalUnsat ->
    False := by
  intro contract
  intro no_claim_blocks_unsat
  intro unsat
  exact no_claim_blocks_unsat
    (ay_usrl_unavailable_no_claim missingEntry evictedEntry fallbackNoClaim
      (ay_usrl_unavailable_contract_state
        validatorExitCode auditDigest acceptedReport missingEntry evictedEntry
        fallbackNoClaim contract))
    unsat
