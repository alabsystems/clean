-- SAT-COMP validator no-claim audit trail core.
--
-- Whenever ay declines a public SAT/UNSAT claim, the audit trail records a
-- diagnostic reason, blocked publication, recompute obligation, manifest
-- digest, exit-code state, and fallback path.  Such entries cannot be upgraded
-- to SAT/UNSAT without fresh accepted evidence.

def ay_vnat_conj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def ay_vnat_disj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def ay_vnat_public_result
    (satFact unsatFact noClaimFact : Prop) : Prop :=
  ay_vnat_disj satFact (ay_vnat_disj unsatFact noClaimFact)

def ay_vnat_blocked_public_result
    (satFact unsatFact reason : Prop) : Prop :=
  ay_vnat_conj reason
    (ay_vnat_conj (satFact -> False) (unsatFact -> False))

def ay_vnat_recompute_obligation
    (reason manifestDigest fallbackPath : Prop) : Prop :=
  ay_vnat_conj reason (ay_vnat_conj manifestDigest fallbackPath)

def ay_vnat_audit_record
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) : Prop :=
  ay_vnat_conj diagnosticReason
    (ay_vnat_conj blockedPublicResult
      (ay_vnat_conj recomputeObligation
        (ay_vnat_conj manifestDigest
          (ay_vnat_conj exitCodeState fallbackPath))))

def ay_vnat_no_claim_entry
    (auditRecord noSemanticClaim : Prop) : Prop :=
  ay_vnat_conj auditRecord noSemanticClaim

def ay_vnat_fresh_accepted_evidence
    (checkerReplay manifestDigest reconstruction publicEvidence : Prop) :
    Prop :=
  ay_vnat_conj checkerReplay
    (ay_vnat_conj manifestDigest
      (ay_vnat_conj reconstruction publicEvidence))

def ay_vnat_upgrade_gate
    (noClaimEntry freshAcceptedEvidence publishedFact : Prop) : Prop :=
  ay_vnat_conj noClaimEntry
    (ay_vnat_conj freshAcceptedEvidence publishedFact)

def ay_vnat_failure
    (satFact unsatFact reason manifestDigest fallbackPath : Prop) : Prop :=
  ay_vnat_conj
    (ay_vnat_blocked_public_result satFact unsatFact reason)
    (ay_vnat_recompute_obligation reason manifestDigest fallbackPath)

theorem ay_vnat_conj_intro (left right : Prop) :
    left -> right -> ay_vnat_conj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vnat_conj_left (left right : Prop) :
    ay_vnat_conj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vnat_conj_right (left right : Prop) :
    ay_vnat_conj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vnat_disj_left (left right : Prop) :
    left -> ay_vnat_disj left right :=
  fun hleft result onLeft _onRight => onLeft hleft

theorem ay_vnat_disj_right (left right : Prop) :
    right -> ay_vnat_disj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vnat_blocked_public_result_intro
    (satFact unsatFact reason : Prop) :
    reason -> (satFact -> False) -> (unsatFact -> False) ->
    ay_vnat_blocked_public_result satFact unsatFact reason :=
  fun reasonProof blockSat blockUnsat =>
    ay_vnat_conj_intro reason
      (ay_vnat_conj (satFact -> False) (unsatFact -> False))
      reasonProof
      (ay_vnat_conj_intro (satFact -> False) (unsatFact -> False)
        blockSat blockUnsat)

theorem ay_vnat_blocked_public_result_reason
    (satFact unsatFact reason : Prop) :
    ay_vnat_blocked_public_result satFact unsatFact reason -> reason :=
  fun blocked =>
    ay_vnat_conj_left reason
      (ay_vnat_conj (satFact -> False) (unsatFact -> False))
      blocked

theorem ay_vnat_blocked_public_result_no_sat
    (satFact unsatFact reason : Prop) :
    ay_vnat_blocked_public_result satFact unsatFact reason ->
    satFact -> False :=
  fun blocked =>
    ay_vnat_conj_right reason
      (ay_vnat_conj (satFact -> False) (unsatFact -> False))
      blocked (satFact -> False)
      (fun blockSat _blockUnsat => blockSat)

theorem ay_vnat_blocked_public_result_no_unsat
    (satFact unsatFact reason : Prop) :
    ay_vnat_blocked_public_result satFact unsatFact reason ->
    unsatFact -> False :=
  fun blocked =>
    ay_vnat_conj_right reason
      (ay_vnat_conj (satFact -> False) (unsatFact -> False))
      blocked (unsatFact -> False)
      (fun _blockSat blockUnsat => blockUnsat)

theorem ay_vnat_recompute_obligation_intro
    (reason manifestDigest fallbackPath : Prop) :
    reason -> manifestDigest -> fallbackPath ->
    ay_vnat_recompute_obligation reason manifestDigest fallbackPath :=
  fun reasonProof digestProof fallbackProof =>
    ay_vnat_conj_intro reason
      (ay_vnat_conj manifestDigest fallbackPath)
      reasonProof
      (ay_vnat_conj_intro manifestDigest fallbackPath digestProof
        fallbackProof)

theorem ay_vnat_recompute_obligation_reason
    (reason manifestDigest fallbackPath : Prop) :
    ay_vnat_recompute_obligation reason manifestDigest fallbackPath ->
    reason :=
  fun recompute =>
    ay_vnat_conj_left reason
      (ay_vnat_conj manifestDigest fallbackPath)
      recompute

theorem ay_vnat_recompute_obligation_digest
    (reason manifestDigest fallbackPath : Prop) :
    ay_vnat_recompute_obligation reason manifestDigest fallbackPath ->
    manifestDigest :=
  fun recompute =>
    ay_vnat_conj_right reason
      (ay_vnat_conj manifestDigest fallbackPath)
      recompute manifestDigest
      (fun digestProof _fallbackProof => digestProof)

theorem ay_vnat_recompute_obligation_fallback
    (reason manifestDigest fallbackPath : Prop) :
    ay_vnat_recompute_obligation reason manifestDigest fallbackPath ->
    fallbackPath :=
  fun recompute =>
    ay_vnat_conj_right reason
      (ay_vnat_conj manifestDigest fallbackPath)
      recompute fallbackPath
      (fun _digestProof fallbackProof => fallbackProof)

theorem ay_vnat_audit_record_intro
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) :
    diagnosticReason -> blockedPublicResult -> recomputeObligation ->
    manifestDigest -> exitCodeState -> fallbackPath ->
    ay_vnat_audit_record diagnosticReason blockedPublicResult
      recomputeObligation manifestDigest exitCodeState fallbackPath :=
  fun reasonProof blockedProof recomputeProof digestProof exitProof
      fallbackProof =>
    ay_vnat_conj_intro diagnosticReason
      (ay_vnat_conj blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))))
      reasonProof
      (ay_vnat_conj_intro blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath)))
        blockedProof
        (ay_vnat_conj_intro recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))
          recomputeProof
          (ay_vnat_conj_intro manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath)
            digestProof
            (ay_vnat_conj_intro exitCodeState fallbackPath exitProof
              fallbackProof))))

theorem ay_vnat_audit_record_reason
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) :
    ay_vnat_audit_record diagnosticReason blockedPublicResult
      recomputeObligation manifestDigest exitCodeState fallbackPath ->
    diagnosticReason :=
  fun record =>
    ay_vnat_conj_left diagnosticReason
      (ay_vnat_conj blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))))
      record

theorem ay_vnat_audit_record_blocked
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) :
    ay_vnat_audit_record diagnosticReason blockedPublicResult
      recomputeObligation manifestDigest exitCodeState fallbackPath ->
    blockedPublicResult :=
  fun record =>
    ay_vnat_conj_right diagnosticReason
      (ay_vnat_conj blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))))
      record blockedPublicResult
      (fun blockedProof _tail => blockedProof)

theorem ay_vnat_audit_record_recompute
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) :
    ay_vnat_audit_record diagnosticReason blockedPublicResult
      recomputeObligation manifestDigest exitCodeState fallbackPath ->
    recomputeObligation :=
  fun record =>
    ay_vnat_conj_right diagnosticReason
      (ay_vnat_conj blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))))
      record recomputeObligation
      (fun _blockedProof tail =>
        tail recomputeObligation
          (fun recomputeProof _tail2 => recomputeProof))

theorem ay_vnat_audit_record_manifest_digest
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) :
    ay_vnat_audit_record diagnosticReason blockedPublicResult
      recomputeObligation manifestDigest exitCodeState fallbackPath ->
    manifestDigest :=
  fun record =>
    ay_vnat_conj_right diagnosticReason
      (ay_vnat_conj blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))))
      record manifestDigest
      (fun _blockedProof tail =>
        tail manifestDigest
          (fun _recomputeProof tail2 =>
            tail2 manifestDigest
              (fun digestProof _tail3 => digestProof)))

theorem ay_vnat_audit_record_exit_code_state
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) :
    ay_vnat_audit_record diagnosticReason blockedPublicResult
      recomputeObligation manifestDigest exitCodeState fallbackPath ->
    exitCodeState :=
  fun record =>
    ay_vnat_conj_right diagnosticReason
      (ay_vnat_conj blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))))
      record exitCodeState
      (fun _blockedProof tail =>
        tail exitCodeState
          (fun _recomputeProof tail2 =>
            tail2 exitCodeState
              (fun _digestProof tail3 =>
                tail3 exitCodeState
                  (fun exitProof _fallbackProof => exitProof))))

theorem ay_vnat_audit_record_fallback_path
    (diagnosticReason blockedPublicResult recomputeObligation manifestDigest
      exitCodeState fallbackPath : Prop) :
    ay_vnat_audit_record diagnosticReason blockedPublicResult
      recomputeObligation manifestDigest exitCodeState fallbackPath ->
    fallbackPath :=
  fun record =>
    ay_vnat_conj_right diagnosticReason
      (ay_vnat_conj blockedPublicResult
        (ay_vnat_conj recomputeObligation
          (ay_vnat_conj manifestDigest
            (ay_vnat_conj exitCodeState fallbackPath))))
      record fallbackPath
      (fun _blockedProof tail =>
        tail fallbackPath
          (fun _recomputeProof tail2 =>
            tail2 fallbackPath
              (fun _digestProof tail3 =>
                tail3 fallbackPath
                  (fun _exitProof fallbackProof => fallbackProof))))

theorem ay_vnat_no_claim_entry_intro
    (auditRecord noSemanticClaim : Prop) :
    auditRecord -> noSemanticClaim ->
    ay_vnat_no_claim_entry auditRecord noSemanticClaim :=
  fun auditProof noClaimProof =>
    ay_vnat_conj_intro auditRecord noSemanticClaim auditProof noClaimProof

theorem ay_vnat_no_claim_entry_audit
    (auditRecord noSemanticClaim : Prop) :
    ay_vnat_no_claim_entry auditRecord noSemanticClaim -> auditRecord :=
  fun entry => ay_vnat_conj_left auditRecord noSemanticClaim entry

theorem ay_vnat_no_claim_entry_no_semantic_claim
    (auditRecord noSemanticClaim : Prop) :
    ay_vnat_no_claim_entry auditRecord noSemanticClaim -> noSemanticClaim :=
  fun entry => ay_vnat_conj_right auditRecord noSemanticClaim entry

theorem ay_vnat_fresh_accepted_evidence_intro
    (checkerReplay manifestDigest reconstruction publicEvidence : Prop) :
    checkerReplay -> manifestDigest -> reconstruction -> publicEvidence ->
    ay_vnat_fresh_accepted_evidence checkerReplay manifestDigest
      reconstruction publicEvidence :=
  fun replayProof digestProof reconstructionProof publicProof =>
    ay_vnat_conj_intro checkerReplay
      (ay_vnat_conj manifestDigest
        (ay_vnat_conj reconstruction publicEvidence))
      replayProof
      (ay_vnat_conj_intro manifestDigest
        (ay_vnat_conj reconstruction publicEvidence)
        digestProof
        (ay_vnat_conj_intro reconstruction publicEvidence
          reconstructionProof publicProof))

theorem ay_vnat_fresh_accepted_evidence_public
    (checkerReplay manifestDigest reconstruction publicEvidence : Prop) :
    ay_vnat_fresh_accepted_evidence checkerReplay manifestDigest
      reconstruction publicEvidence ->
    publicEvidence :=
  fun evidence =>
    ay_vnat_conj_right checkerReplay
      (ay_vnat_conj manifestDigest
        (ay_vnat_conj reconstruction publicEvidence))
      evidence publicEvidence
      (fun _digestProof tail =>
        tail publicEvidence
          (fun _reconstructionProof publicProof => publicProof))

theorem ay_vnat_upgrade_gate_intro
    (noClaimEntry freshAcceptedEvidence publishedFact : Prop) :
    noClaimEntry -> freshAcceptedEvidence -> publishedFact ->
    ay_vnat_upgrade_gate noClaimEntry freshAcceptedEvidence publishedFact :=
  fun noClaimProof evidenceProof publishedProof =>
    ay_vnat_conj_intro noClaimEntry
      (ay_vnat_conj freshAcceptedEvidence publishedFact)
      noClaimProof
      (ay_vnat_conj_intro freshAcceptedEvidence publishedFact
        evidenceProof publishedProof)

theorem ay_vnat_upgrade_gate_fresh_evidence
    (noClaimEntry freshAcceptedEvidence publishedFact : Prop) :
    ay_vnat_upgrade_gate noClaimEntry freshAcceptedEvidence publishedFact ->
    freshAcceptedEvidence :=
  fun gate =>
    ay_vnat_conj_right noClaimEntry
      (ay_vnat_conj freshAcceptedEvidence publishedFact)
      gate freshAcceptedEvidence
      (fun evidenceProof _publishedProof => evidenceProof)

theorem ay_vnat_upgrade_gate_published
    (noClaimEntry freshAcceptedEvidence publishedFact : Prop) :
    ay_vnat_upgrade_gate noClaimEntry freshAcceptedEvidence publishedFact ->
    publishedFact :=
  fun gate =>
    ay_vnat_conj_right noClaimEntry
      (ay_vnat_conj freshAcceptedEvidence publishedFact)
      gate publishedFact
      (fun _evidenceProof publishedProof => publishedProof)

theorem ay_vnat_no_claim_requires_fresh_evidence_to_upgrade
    (auditRecord noSemanticClaim freshAcceptedEvidence publishedFact : Prop) :
    ay_vnat_upgrade_gate
      (ay_vnat_no_claim_entry auditRecord noSemanticClaim)
      freshAcceptedEvidence publishedFact ->
    freshAcceptedEvidence :=
  ay_vnat_upgrade_gate_fresh_evidence
    (ay_vnat_no_claim_entry auditRecord noSemanticClaim)
    freshAcceptedEvidence publishedFact

theorem ay_vnat_no_claim_public_result
    (satFact unsatFact auditRecord noSemanticClaim : Prop) :
    ay_vnat_no_claim_entry auditRecord noSemanticClaim ->
    ay_vnat_public_result satFact unsatFact noSemanticClaim :=
  fun entry =>
    ay_vnat_disj_right satFact
      (ay_vnat_disj unsatFact noSemanticClaim)
      (ay_vnat_disj_right unsatFact noSemanticClaim
        (ay_vnat_no_claim_entry_no_semantic_claim auditRecord
          noSemanticClaim entry))

theorem ay_vnat_failure_intro
    (satFact unsatFact reason manifestDigest fallbackPath : Prop) :
    ay_vnat_blocked_public_result satFact unsatFact reason ->
    ay_vnat_recompute_obligation reason manifestDigest fallbackPath ->
    ay_vnat_failure satFact unsatFact reason manifestDigest fallbackPath :=
  fun blocked recompute =>
    ay_vnat_conj_intro
      (ay_vnat_blocked_public_result satFact unsatFact reason)
      (ay_vnat_recompute_obligation reason manifestDigest fallbackPath)
      blocked recompute

theorem ay_vnat_failure_blocks_sat
    (satFact unsatFact reason manifestDigest fallbackPath : Prop) :
    ay_vnat_failure satFact unsatFact reason manifestDigest fallbackPath ->
    satFact -> False :=
  fun failure =>
    ay_vnat_blocked_public_result_no_sat satFact unsatFact reason
      (ay_vnat_conj_left
        (ay_vnat_blocked_public_result satFact unsatFact reason)
        (ay_vnat_recompute_obligation reason manifestDigest fallbackPath)
        failure)

theorem ay_vnat_failure_blocks_unsat
    (satFact unsatFact reason manifestDigest fallbackPath : Prop) :
    ay_vnat_failure satFact unsatFact reason manifestDigest fallbackPath ->
    unsatFact -> False :=
  fun failure =>
    ay_vnat_blocked_public_result_no_unsat satFact unsatFact reason
      (ay_vnat_conj_left
        (ay_vnat_blocked_public_result satFact unsatFact reason)
        (ay_vnat_recompute_obligation reason manifestDigest fallbackPath)
        failure)

theorem ay_vnat_failure_recompute
    (satFact unsatFact reason manifestDigest fallbackPath : Prop) :
    ay_vnat_failure satFact unsatFact reason manifestDigest fallbackPath ->
    ay_vnat_recompute_obligation reason manifestDigest fallbackPath :=
  fun failure =>
    ay_vnat_conj_right
      (ay_vnat_blocked_public_result satFact unsatFact reason)
      (ay_vnat_recompute_obligation reason manifestDigest fallbackPath)
      failure

theorem ay_vnat_stale_audit_trail_forces_recompute
    (satFact unsatFact staleAudit manifestDigest fallbackPath : Prop) :
    staleAudit -> (satFact -> False) -> (unsatFact -> False) ->
    manifestDigest -> fallbackPath ->
    ay_vnat_failure satFact unsatFact staleAudit manifestDigest
      fallbackPath :=
  fun reasonProof blockSat blockUnsat digestProof fallbackProof =>
    ay_vnat_failure_intro satFact unsatFact staleAudit manifestDigest
      fallbackPath
      (ay_vnat_blocked_public_result_intro satFact unsatFact staleAudit
        reasonProof blockSat blockUnsat)
      (ay_vnat_recompute_obligation_intro staleAudit manifestDigest
        fallbackPath reasonProof digestProof fallbackProof)

theorem ay_vnat_contradictory_audit_trail_forces_recompute
    (satFact unsatFact contradiction manifestDigest fallbackPath : Prop) :
    contradiction -> (satFact -> False) -> (unsatFact -> False) ->
    manifestDigest -> fallbackPath ->
    ay_vnat_failure satFact unsatFact contradiction manifestDigest
      fallbackPath :=
  fun reasonProof blockSat blockUnsat digestProof fallbackProof =>
    ay_vnat_failure_intro satFact unsatFact contradiction manifestDigest
      fallbackPath
      (ay_vnat_blocked_public_result_intro satFact unsatFact contradiction
        reasonProof blockSat blockUnsat)
      (ay_vnat_recompute_obligation_intro contradiction manifestDigest
        fallbackPath reasonProof digestProof fallbackProof)

theorem ay_vnat_failure_cannot_publish_sat
    (satFact unsatFact reason manifestDigest fallbackPath : Prop) :
    ay_vnat_failure satFact unsatFact reason manifestDigest fallbackPath ->
    satFact -> False :=
  ay_vnat_failure_blocks_sat satFact unsatFact reason manifestDigest
    fallbackPath

theorem ay_vnat_failure_cannot_publish_unsat
    (satFact unsatFact reason manifestDigest fallbackPath : Prop) :
    ay_vnat_failure satFact unsatFact reason manifestDigest fallbackPath ->
    unsatFact -> False :=
  ay_vnat_failure_blocks_unsat satFact unsatFact reason manifestDigest
    fallbackPath
