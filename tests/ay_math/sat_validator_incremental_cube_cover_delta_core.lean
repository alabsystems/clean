-- SAT-COMP validator incremental cube-cover delta core.
--
-- Incremental cube-cover validation may update a previously accepted aggregate
-- only when the delta preserves formula fingerprint, cube-frame lineage,
-- replaced-cube coverage, replay evidence for new cubes, and audit linkage
-- between old and new manifests.  Bad deltas are no-claim recomputation cases.

def AyVICDConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVICDDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVICDEquisat (before after : Prop) : Prop :=
  AyVICDConj (before -> after) (after -> before)

def AyVICDPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVICDDisj satFact (AyVICDDisj unsatFact noClaim)

def AyVICDDeltaEvidence
    (formulaFingerprint frameLineage replacedCoverage newCubeReplay
      manifestAudit : Prop) : Prop :=
  AyVICDConj formulaFingerprint
    (AyVICDConj frameLineage
      (AyVICDConj replacedCoverage
        (AyVICDConj newCubeReplay manifestAudit)))

def AyVICDPriorAggregate
    (oldManifest oldCover oldPublicResult : Prop) : Prop :=
  AyVICDConj oldManifest (AyVICDConj oldCover oldPublicResult)

def AyVICDAcceptedDelta
    (priorAggregate deltaEvidence newManifest updatedAggregate : Prop) :
    Prop :=
  AyVICDConj priorAggregate
    (AyVICDConj deltaEvidence
      (AyVICDConj newManifest updatedAggregate))

def AyVICDEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVICDConj exitCode
    (AyVICDConj artifacts
      (AyVICDConj checkerDecision
        (AyVICDConj auditDigest diagnostic)))

def AyVICDMembership (leafHash root entry : Prop) : Prop :=
  AyVICDConj leafHash (AyVICDConj root entry)

def AyVICDNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVICDConj reason (AyVICDConj auditDigest diagnostic)

def AyVICDRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVICDConj reason (AyVICDConj auditDigest diagnostic)

def AyVICDModel (formula assignment : Prop) : Prop :=
  AyVICDConj formula assignment

def AyVICDUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVICDVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVICDModel original visibleAssignment

def AyVICDPreprocessArtifact (original solver : Prop) : Prop :=
  AyVICDEquisat original solver

def AyVICDReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vicd_conj_intro (left right : Prop) :
    left -> right -> AyVICDConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vicd_conj_left (left right : Prop) :
    AyVICDConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vicd_conj_right (left right : Prop) :
    AyVICDConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vicd_disj_right (left right : Prop) :
    right -> AyVICDDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vicd_equisat_forward (before after : Prop) :
    AyVICDEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vicd_equisat_backward (before after : Prop) :
    AyVICDEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vicd_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVICDModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vicd_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vicd_model_formula (formula assignment : Prop) :
    AyVICDModel formula assignment -> formula :=
  fun model => ay_vicd_conj_left formula assignment model

theorem ay_vicd_model_assignment (formula assignment : Prop) :
    AyVICDModel formula assignment -> assignment :=
  fun model => ay_vicd_conj_right formula assignment model

theorem ay_vicd_delta_evidence_intro
    (formulaFingerprint frameLineage replacedCoverage newCubeReplay
      manifestAudit : Prop) :
    formulaFingerprint -> frameLineage -> replacedCoverage ->
    newCubeReplay -> manifestAudit ->
    AyVICDDeltaEvidence formulaFingerprint frameLineage replacedCoverage
      newCubeReplay manifestAudit :=
  fun fingerprintProof lineageProof coverageProof replayProof auditProof =>
    ay_vicd_conj_intro formulaFingerprint
      (AyVICDConj frameLineage
        (AyVICDConj replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit)))
      fingerprintProof
      (ay_vicd_conj_intro frameLineage
        (AyVICDConj replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit))
        lineageProof
        (ay_vicd_conj_intro replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit)
          coverageProof
          (ay_vicd_conj_intro newCubeReplay manifestAudit replayProof
            auditProof)))

theorem ay_vicd_delta_evidence_fingerprint
    (formulaFingerprint frameLineage replacedCoverage newCubeReplay
      manifestAudit : Prop) :
    AyVICDDeltaEvidence formulaFingerprint frameLineage replacedCoverage
      newCubeReplay manifestAudit ->
    formulaFingerprint :=
  fun evidence =>
    ay_vicd_conj_left formulaFingerprint
      (AyVICDConj frameLineage
        (AyVICDConj replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit)))
      evidence

theorem ay_vicd_delta_evidence_lineage
    (formulaFingerprint frameLineage replacedCoverage newCubeReplay
      manifestAudit : Prop) :
    AyVICDDeltaEvidence formulaFingerprint frameLineage replacedCoverage
      newCubeReplay manifestAudit ->
    frameLineage :=
  fun evidence =>
    ay_vicd_conj_right formulaFingerprint
      (AyVICDConj frameLineage
        (AyVICDConj replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit)))
      evidence frameLineage (fun lineageProof _tail => lineageProof)

theorem ay_vicd_delta_evidence_coverage
    (formulaFingerprint frameLineage replacedCoverage newCubeReplay
      manifestAudit : Prop) :
    AyVICDDeltaEvidence formulaFingerprint frameLineage replacedCoverage
      newCubeReplay manifestAudit ->
    replacedCoverage :=
  fun evidence =>
    ay_vicd_conj_right formulaFingerprint
      (AyVICDConj frameLineage
        (AyVICDConj replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit)))
      evidence replacedCoverage
      (fun _lineageProof tail =>
        tail replacedCoverage (fun coverageProof _tail2 =>
          coverageProof))

theorem ay_vicd_delta_evidence_replay
    (formulaFingerprint frameLineage replacedCoverage newCubeReplay
      manifestAudit : Prop) :
    AyVICDDeltaEvidence formulaFingerprint frameLineage replacedCoverage
      newCubeReplay manifestAudit ->
    newCubeReplay :=
  fun evidence =>
    ay_vicd_conj_right formulaFingerprint
      (AyVICDConj frameLineage
        (AyVICDConj replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit)))
      evidence newCubeReplay
      (fun _lineageProof tail =>
        tail newCubeReplay
          (fun _coverageProof tail2 =>
            tail2 newCubeReplay
              (fun replayProof _auditProof => replayProof)))

theorem ay_vicd_delta_evidence_audit
    (formulaFingerprint frameLineage replacedCoverage newCubeReplay
      manifestAudit : Prop) :
    AyVICDDeltaEvidence formulaFingerprint frameLineage replacedCoverage
      newCubeReplay manifestAudit ->
    manifestAudit :=
  fun evidence =>
    ay_vicd_conj_right formulaFingerprint
      (AyVICDConj frameLineage
        (AyVICDConj replacedCoverage
          (AyVICDConj newCubeReplay manifestAudit)))
      evidence manifestAudit
      (fun _lineageProof tail =>
        tail manifestAudit
          (fun _coverageProof tail2 =>
            tail2 manifestAudit
              (fun _replayProof auditProof => auditProof)))

theorem ay_vicd_prior_aggregate_intro
    (oldManifest oldCover oldPublicResult : Prop) :
    oldManifest -> oldCover -> oldPublicResult ->
    AyVICDPriorAggregate oldManifest oldCover oldPublicResult :=
  fun manifestProof coverProof publicProof =>
    ay_vicd_conj_intro oldManifest
      (AyVICDConj oldCover oldPublicResult)
      manifestProof
      (ay_vicd_conj_intro oldCover oldPublicResult coverProof
        publicProof)

theorem ay_vicd_prior_aggregate_public
    (oldManifest oldCover oldPublicResult : Prop) :
    AyVICDPriorAggregate oldManifest oldCover oldPublicResult ->
    oldPublicResult :=
  fun prior =>
    ay_vicd_conj_right oldManifest
      (AyVICDConj oldCover oldPublicResult)
      prior oldPublicResult (fun _coverProof publicProof => publicProof)

theorem ay_vicd_accepted_delta_intro
    (priorAggregate deltaEvidence newManifest updatedAggregate : Prop) :
    priorAggregate -> deltaEvidence -> newManifest -> updatedAggregate ->
    AyVICDAcceptedDelta priorAggregate deltaEvidence newManifest
      updatedAggregate :=
  fun priorProof evidenceProof manifestProof updatedProof =>
    ay_vicd_conj_intro priorAggregate
      (AyVICDConj deltaEvidence
        (AyVICDConj newManifest updatedAggregate))
      priorProof
      (ay_vicd_conj_intro deltaEvidence
        (AyVICDConj newManifest updatedAggregate)
        evidenceProof
        (ay_vicd_conj_intro newManifest updatedAggregate manifestProof
          updatedProof))

theorem ay_vicd_accepted_delta_prior
    (priorAggregate deltaEvidence newManifest updatedAggregate : Prop) :
    AyVICDAcceptedDelta priorAggregate deltaEvidence newManifest
      updatedAggregate ->
    priorAggregate :=
  fun delta =>
    ay_vicd_conj_left priorAggregate
      (AyVICDConj deltaEvidence
        (AyVICDConj newManifest updatedAggregate))
      delta

theorem ay_vicd_accepted_delta_evidence
    (priorAggregate deltaEvidence newManifest updatedAggregate : Prop) :
    AyVICDAcceptedDelta priorAggregate deltaEvidence newManifest
      updatedAggregate ->
    deltaEvidence :=
  fun delta =>
    ay_vicd_conj_right priorAggregate
      (AyVICDConj deltaEvidence
        (AyVICDConj newManifest updatedAggregate))
      delta deltaEvidence (fun evidenceProof _tail => evidenceProof)

theorem ay_vicd_accepted_delta_updated
    (priorAggregate deltaEvidence newManifest updatedAggregate : Prop) :
    AyVICDAcceptedDelta priorAggregate deltaEvidence newManifest
      updatedAggregate ->
    updatedAggregate :=
  fun delta =>
    ay_vicd_conj_right priorAggregate
      (AyVICDConj deltaEvidence
        (AyVICDConj newManifest updatedAggregate))
      delta updatedAggregate
      (fun _evidenceProof tail =>
        tail updatedAggregate (fun _manifestProof updatedProof =>
          updatedProof))

theorem ay_vicd_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVICDEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vicd_conj_intro exitCode
      (AyVICDConj artifacts
        (AyVICDConj checkerDecision (AyVICDConj auditDigest diagnostic)))
      exitProof
      (ay_vicd_conj_intro artifacts
        (AyVICDConj checkerDecision (AyVICDConj auditDigest diagnostic))
        artifactsProof
        (ay_vicd_conj_intro checkerDecision
          (AyVICDConj auditDigest diagnostic)
          checkerProof
          (ay_vicd_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vicd_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVICDEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vicd_conj_right exitCode
      (AyVICDConj artifacts
        (AyVICDConj checkerDecision (AyVICDConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vicd_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVICDMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vicd_conj_intro leafHash (AyVICDConj root entry)
      leafProof
      (ay_vicd_conj_intro root entry rootProof entryProof)

theorem ay_vicd_membership_entry (leafHash root entry : Prop) :
    AyVICDMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vicd_conj_right leafHash (AyVICDConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vicd_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVICDNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vicd_conj_intro reason (AyVICDConj auditDigest diagnostic)
      reasonProof
      (ay_vicd_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vicd_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVICDRecomputeObligation reason auditDigest diagnostic :=
  ay_vicd_no_claim_intro reason auditDigest diagnostic

theorem ay_vicd_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVICDPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVICDModel solver internalAssignment ->
    AyVICDVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vicd_model_intro original visibleAssignment
      (ay_vicd_equisat_backward original solver preprocess
        (ay_vicd_model_formula solver internalAssignment model))
      (decode (ay_vicd_model_assignment solver internalAssignment model))

theorem ay_vicd_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVICDPreprocessArtifact original solver ->
    AyVICDUnsat solver ->
    AyVICDUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vicd_equisat_forward original solver preprocess originalProof)

theorem ay_vicd_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVICDPreprocessArtifact original solver ->
    AyVICDReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVICDUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vicd_equisat_forward original solver preprocess originalProof))

theorem ay_vicd_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVICDPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVICDModel solver internalAssignment) ->
    AyVICDMembership leafHash root
      (AyVICDEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVICDVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vicd_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vicd_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vicd_membership_entry leafHash root
            (AyVICDEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vicd_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVICDPreprocessArtifact original solver ->
    AyVICDReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVICDMembership leafHash root
      (AyVICDEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVICDUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vicd_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vicd_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vicd_membership_entry leafHash root
            (AyVICDEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vicd_accepted_delta_public_sound
    (priorAggregate deltaEvidence newManifest updatedAggregate
      satFact unsatFact noClaim : Prop) :
    AyVICDAcceptedDelta priorAggregate deltaEvidence newManifest
      updatedAggregate ->
    (priorAggregate -> deltaEvidence -> updatedAggregate ->
      AyVICDPublicResult satFact unsatFact noClaim) ->
    AyVICDPublicResult satFact unsatFact noClaim :=
  fun delta sound =>
    sound
      (ay_vicd_accepted_delta_prior priorAggregate deltaEvidence
        newManifest updatedAggregate delta)
      (ay_vicd_accepted_delta_evidence priorAggregate deltaEvidence
        newManifest updatedAggregate delta)
      (ay_vicd_accepted_delta_updated priorAggregate deltaEvidence
        newManifest updatedAggregate delta)

theorem ay_vicd_accepted_delta_preserves_sat
    (priorAggregate deltaEvidence newManifest updatedAggregate satFact :
      Prop) :
    AyVICDAcceptedDelta priorAggregate deltaEvidence newManifest
      updatedAggregate ->
    (deltaEvidence -> updatedAggregate -> satFact) ->
    satFact :=
  fun delta sound =>
    sound
      (ay_vicd_accepted_delta_evidence priorAggregate deltaEvidence
        newManifest updatedAggregate delta)
      (ay_vicd_accepted_delta_updated priorAggregate deltaEvidence
        newManifest updatedAggregate delta)

theorem ay_vicd_accepted_delta_preserves_unsat
    (priorAggregate deltaEvidence newManifest updatedAggregate unsatFact :
      Prop) :
    AyVICDAcceptedDelta priorAggregate deltaEvidence newManifest
      updatedAggregate ->
    (deltaEvidence -> updatedAggregate -> unsatFact) ->
    unsatFact :=
  fun delta sound =>
    sound
      (ay_vicd_accepted_delta_evidence priorAggregate deltaEvidence
        newManifest updatedAggregate delta)
      (ay_vicd_accepted_delta_updated priorAggregate deltaEvidence
        newManifest updatedAggregate delta)

theorem ay_vicd_dropped_coverage_no_claim
    (droppedCoverage auditDigest diagnostic : Prop) :
    droppedCoverage -> auditDigest -> diagnostic ->
    AyVICDNoClaim droppedCoverage auditDigest diagnostic :=
  ay_vicd_no_claim_intro droppedCoverage auditDigest diagnostic

theorem ay_vicd_stale_frame_lineage_no_claim
    (staleFrameLineage auditDigest diagnostic : Prop) :
    staleFrameLineage -> auditDigest -> diagnostic ->
    AyVICDNoClaim staleFrameLineage auditDigest diagnostic :=
  ay_vicd_no_claim_intro staleFrameLineage auditDigest diagnostic

theorem ay_vicd_missing_replay_no_claim
    (missingReplay auditDigest diagnostic : Prop) :
    missingReplay -> auditDigest -> diagnostic ->
    AyVICDNoClaim missingReplay auditDigest diagnostic :=
  ay_vicd_no_claim_intro missingReplay auditDigest diagnostic

theorem ay_vicd_bad_manifest_link_no_claim
    (badManifestLink auditDigest diagnostic : Prop) :
    badManifestLink -> auditDigest -> diagnostic ->
    AyVICDNoClaim badManifestLink auditDigest diagnostic :=
  ay_vicd_no_claim_intro badManifestLink auditDigest diagnostic

theorem ay_vicd_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVICDNoClaim reason auditDigest diagnostic ->
    AyVICDPublicResult satFact unsatFact
      (AyVICDNoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vicd_disj_right satFact
      (AyVICDDisj unsatFact
        (AyVICDNoClaim reason auditDigest diagnostic))
      (ay_vicd_disj_right unsatFact
        (AyVICDNoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vicd_delta_failure_recompute
    (droppedCoverage staleFrameLineage missingReplay badManifestLink
      auditDigest diagnostic recompute : Prop) :
    AyVICDDisj droppedCoverage
      (AyVICDDisj staleFrameLineage
        (AyVICDDisj missingReplay badManifestLink)) ->
    auditDigest -> diagnostic ->
    (droppedCoverage ->
      AyVICDRecomputeObligation droppedCoverage auditDigest diagnostic ->
      recompute) ->
    (staleFrameLineage ->
      AyVICDRecomputeObligation staleFrameLineage auditDigest diagnostic ->
      recompute) ->
    (missingReplay ->
      AyVICDRecomputeObligation missingReplay auditDigest diagnostic ->
      recompute) ->
    (badManifestLink ->
      AyVICDRecomputeObligation badManifestLink auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onDropped onFrame onReplay
      onManifest =>
    failure recompute
      (fun droppedProof =>
        onDropped droppedProof
          (ay_vicd_recompute_intro droppedCoverage auditDigest diagnostic
            droppedProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun frameProof =>
            onFrame frameProof
              (ay_vicd_recompute_intro staleFrameLineage auditDigest
                diagnostic frameProof auditProof diagnosticProof))
          (fun tail2 =>
            tail2 recompute
              (fun replayProof =>
                onReplay replayProof
                  (ay_vicd_recompute_intro missingReplay auditDigest
                    diagnostic replayProof auditProof diagnosticProof))
              (fun manifestProof =>
                onManifest manifestProof
                  (ay_vicd_recompute_intro badManifestLink auditDigest
                    diagnostic manifestProof auditProof diagnosticProof)))
