-- SAT-COMP validator cube-cover completion soundness core.
--
-- A cube-cover batch proves a base formula result only when every cube has
-- matching frame evidence and SAT/UNSAT/no-claim checker evidence.  Incomplete
-- covers or no-claim cubes lift to batch-level no-claim/recompute.

def AyVCCCConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVCCCDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVCCCEquisat (before after : Prop) : Prop :=
  AyVCCCConj (before -> after) (after -> before)

def AyVCCCPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVCCCDisj satFact (AyVCCCDisj unsatFact noClaim)

def AyVCCCCubeEvidence
    (cubeFrame checkerEvidence cubeResult publicLabel : Prop) : Prop :=
  AyVCCCConj cubeFrame
    (AyVCCCConj checkerEvidence
      (AyVCCCConj cubeResult publicLabel))

def AyVCCCCoverEvidence
    (baseFormula completeCover allCubeFrames allCubeEvidence : Prop) :
    Prop :=
  AyVCCCConj baseFormula
    (AyVCCCConj completeCover
      (AyVCCCConj allCubeFrames allCubeEvidence))

def AyVCCCBatchAggregation
    (coverEvidence aggregateChecker publicResult : Prop) : Prop :=
  AyVCCCConj coverEvidence (AyVCCCConj aggregateChecker publicResult)

def AyVCCCEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVCCCConj exitCode
    (AyVCCCConj artifacts
      (AyVCCCConj checkerDecision
        (AyVCCCConj auditDigest diagnostic)))

def AyVCCCMembership (leafHash root entry : Prop) : Prop :=
  AyVCCCConj leafHash (AyVCCCConj root entry)

def AyVCCCNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCCCConj reason (AyVCCCConj auditDigest diagnostic)

def AyVCCCRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCCCConj reason (AyVCCCConj auditDigest diagnostic)

def AyVCCCModel (formula assignment : Prop) : Prop :=
  AyVCCCConj formula assignment

def AyVCCCUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVCCCVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVCCCModel original visibleAssignment

def AyVCCCPreprocessArtifact (original solver : Prop) : Prop :=
  AyVCCCEquisat original solver

def AyVCCCReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vccc_conj_intro (left right : Prop) :
    left -> right -> AyVCCCConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vccc_conj_left (left right : Prop) :
    AyVCCCConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vccc_conj_right (left right : Prop) :
    AyVCCCConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vccc_disj_right (left right : Prop) :
    right -> AyVCCCDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vccc_equisat_forward (before after : Prop) :
    AyVCCCEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vccc_equisat_backward (before after : Prop) :
    AyVCCCEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vccc_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVCCCModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vccc_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vccc_model_formula (formula assignment : Prop) :
    AyVCCCModel formula assignment -> formula :=
  fun model => ay_vccc_conj_left formula assignment model

theorem ay_vccc_model_assignment (formula assignment : Prop) :
    AyVCCCModel formula assignment -> assignment :=
  fun model => ay_vccc_conj_right formula assignment model

theorem ay_vccc_cube_evidence_intro
    (cubeFrame checkerEvidence cubeResult publicLabel : Prop) :
    cubeFrame -> checkerEvidence -> cubeResult -> publicLabel ->
    AyVCCCCubeEvidence cubeFrame checkerEvidence cubeResult publicLabel :=
  fun frameProof checkerProof resultProof labelProof =>
    ay_vccc_conj_intro cubeFrame
      (AyVCCCConj checkerEvidence
        (AyVCCCConj cubeResult publicLabel))
      frameProof
      (ay_vccc_conj_intro checkerEvidence
        (AyVCCCConj cubeResult publicLabel)
        checkerProof
        (ay_vccc_conj_intro cubeResult publicLabel resultProof labelProof))

theorem ay_vccc_cube_evidence_frame
    (cubeFrame checkerEvidence cubeResult publicLabel : Prop) :
    AyVCCCCubeEvidence cubeFrame checkerEvidence cubeResult publicLabel ->
    cubeFrame :=
  fun evidence =>
    ay_vccc_conj_left cubeFrame
      (AyVCCCConj checkerEvidence
        (AyVCCCConj cubeResult publicLabel))
      evidence

theorem ay_vccc_cube_evidence_checker
    (cubeFrame checkerEvidence cubeResult publicLabel : Prop) :
    AyVCCCCubeEvidence cubeFrame checkerEvidence cubeResult publicLabel ->
    checkerEvidence :=
  fun evidence =>
    ay_vccc_conj_right cubeFrame
      (AyVCCCConj checkerEvidence
        (AyVCCCConj cubeResult publicLabel))
      evidence checkerEvidence (fun checkerProof _tail => checkerProof)

theorem ay_vccc_cover_evidence_intro
    (baseFormula completeCover allCubeFrames allCubeEvidence : Prop) :
    baseFormula -> completeCover -> allCubeFrames -> allCubeEvidence ->
    AyVCCCCoverEvidence baseFormula completeCover allCubeFrames
      allCubeEvidence :=
  fun baseProof completeProof framesProof evidenceProof =>
    ay_vccc_conj_intro baseFormula
      (AyVCCCConj completeCover
        (AyVCCCConj allCubeFrames allCubeEvidence))
      baseProof
      (ay_vccc_conj_intro completeCover
        (AyVCCCConj allCubeFrames allCubeEvidence)
        completeProof
        (ay_vccc_conj_intro allCubeFrames allCubeEvidence framesProof
          evidenceProof))

theorem ay_vccc_cover_evidence_complete
    (baseFormula completeCover allCubeFrames allCubeEvidence : Prop) :
    AyVCCCCoverEvidence baseFormula completeCover allCubeFrames
      allCubeEvidence ->
    completeCover :=
  fun cover =>
    ay_vccc_conj_right baseFormula
      (AyVCCCConj completeCover
        (AyVCCCConj allCubeFrames allCubeEvidence))
      cover completeCover (fun completeProof _tail => completeProof)

theorem ay_vccc_cover_evidence_frames
    (baseFormula completeCover allCubeFrames allCubeEvidence : Prop) :
    AyVCCCCoverEvidence baseFormula completeCover allCubeFrames
      allCubeEvidence ->
    allCubeFrames :=
  fun cover =>
    ay_vccc_conj_right baseFormula
      (AyVCCCConj completeCover
        (AyVCCCConj allCubeFrames allCubeEvidence))
      cover allCubeFrames
      (fun _completeProof tail =>
        tail allCubeFrames
          (fun framesProof _evidenceProof => framesProof))

theorem ay_vccc_cover_evidence_all_cubes
    (baseFormula completeCover allCubeFrames allCubeEvidence : Prop) :
    AyVCCCCoverEvidence baseFormula completeCover allCubeFrames
      allCubeEvidence ->
    allCubeEvidence :=
  fun cover =>
    ay_vccc_conj_right baseFormula
      (AyVCCCConj completeCover
        (AyVCCCConj allCubeFrames allCubeEvidence))
      cover allCubeEvidence
      (fun _completeProof tail =>
        tail allCubeEvidence
          (fun _framesProof evidenceProof => evidenceProof))

theorem ay_vccc_batch_aggregation_intro
    (coverEvidence aggregateChecker publicResult : Prop) :
    coverEvidence -> aggregateChecker -> publicResult ->
    AyVCCCBatchAggregation coverEvidence aggregateChecker publicResult :=
  fun coverProof checkerProof publicProof =>
    ay_vccc_conj_intro coverEvidence
      (AyVCCCConj aggregateChecker publicResult)
      coverProof
      (ay_vccc_conj_intro aggregateChecker publicResult checkerProof
        publicProof)

theorem ay_vccc_batch_aggregation_cover
    (coverEvidence aggregateChecker publicResult : Prop) :
    AyVCCCBatchAggregation coverEvidence aggregateChecker publicResult ->
    coverEvidence :=
  fun aggregation =>
    ay_vccc_conj_left coverEvidence
      (AyVCCCConj aggregateChecker publicResult) aggregation

theorem ay_vccc_batch_aggregation_checker
    (coverEvidence aggregateChecker publicResult : Prop) :
    AyVCCCBatchAggregation coverEvidence aggregateChecker publicResult ->
    aggregateChecker :=
  fun aggregation =>
    ay_vccc_conj_right coverEvidence
      (AyVCCCConj aggregateChecker publicResult)
      aggregation aggregateChecker
      (fun checkerProof _publicProof => checkerProof)

theorem ay_vccc_batch_aggregation_public
    (coverEvidence aggregateChecker publicResult : Prop) :
    AyVCCCBatchAggregation coverEvidence aggregateChecker publicResult ->
    publicResult :=
  fun aggregation =>
    ay_vccc_conj_right coverEvidence
      (AyVCCCConj aggregateChecker publicResult)
      aggregation publicResult
      (fun _checkerProof publicProof => publicProof)

theorem ay_vccc_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVCCCEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vccc_conj_intro exitCode
      (AyVCCCConj artifacts
        (AyVCCCConj checkerDecision (AyVCCCConj auditDigest diagnostic)))
      exitProof
      (ay_vccc_conj_intro artifacts
        (AyVCCCConj checkerDecision (AyVCCCConj auditDigest diagnostic))
        artifactsProof
        (ay_vccc_conj_intro checkerDecision
          (AyVCCCConj auditDigest diagnostic)
          checkerProof
          (ay_vccc_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vccc_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVCCCEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vccc_conj_right exitCode
      (AyVCCCConj artifacts
        (AyVCCCConj checkerDecision (AyVCCCConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vccc_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVCCCMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vccc_conj_intro leafHash (AyVCCCConj root entry)
      leafProof
      (ay_vccc_conj_intro root entry rootProof entryProof)

theorem ay_vccc_membership_entry (leafHash root entry : Prop) :
    AyVCCCMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vccc_conj_right leafHash (AyVCCCConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vccc_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCCCNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vccc_conj_intro reason (AyVCCCConj auditDigest diagnostic)
      reasonProof
      (ay_vccc_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vccc_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCCCRecomputeObligation reason auditDigest diagnostic :=
  ay_vccc_no_claim_intro reason auditDigest diagnostic

theorem ay_vccc_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVCCCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVCCCModel solver internalAssignment ->
    AyVCCCVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vccc_model_intro original visibleAssignment
      (ay_vccc_equisat_backward original solver preprocess
        (ay_vccc_model_formula solver internalAssignment model))
      (decode (ay_vccc_model_assignment solver internalAssignment model))

theorem ay_vccc_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVCCCPreprocessArtifact original solver ->
    AyVCCCUnsat solver ->
    AyVCCCUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vccc_equisat_forward original solver preprocess originalProof)

theorem ay_vccc_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVCCCPreprocessArtifact original solver ->
    AyVCCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVCCCUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vccc_equisat_forward original solver preprocess originalProof))

theorem ay_vccc_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVCCCPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVCCCModel solver internalAssignment) ->
    AyVCCCMembership leafHash root
      (AyVCCCEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVCCCVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vccc_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vccc_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vccc_membership_entry leafHash root
            (AyVCCCEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vccc_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVCCCPreprocessArtifact original solver ->
    AyVCCCReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVCCCMembership leafHash root
      (AyVCCCEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVCCCUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vccc_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vccc_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vccc_membership_entry leafHash root
            (AyVCCCEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vccc_complete_cover_public_sound
    (coverEvidence aggregateChecker publicResult satFact unsatFact
      noClaim : Prop) :
    AyVCCCBatchAggregation coverEvidence aggregateChecker publicResult ->
    (coverEvidence -> aggregateChecker -> publicResult ->
      AyVCCCPublicResult satFact unsatFact noClaim) ->
    AyVCCCPublicResult satFact unsatFact noClaim :=
  fun aggregation sound =>
    sound
      (ay_vccc_batch_aggregation_cover coverEvidence aggregateChecker
        publicResult aggregation)
      (ay_vccc_batch_aggregation_checker coverEvidence aggregateChecker
        publicResult aggregation)
      (ay_vccc_batch_aggregation_public coverEvidence aggregateChecker
        publicResult aggregation)

theorem ay_vccc_complete_cover_preserves_sat
    (coverEvidence aggregateChecker publicResult satFact : Prop) :
    AyVCCCBatchAggregation coverEvidence aggregateChecker publicResult ->
    (coverEvidence -> aggregateChecker -> satFact) ->
    satFact :=
  fun aggregation sound =>
    sound
      (ay_vccc_batch_aggregation_cover coverEvidence aggregateChecker
        publicResult aggregation)
      (ay_vccc_batch_aggregation_checker coverEvidence aggregateChecker
        publicResult aggregation)

theorem ay_vccc_complete_cover_preserves_unsat
    (coverEvidence aggregateChecker publicResult unsatFact : Prop) :
    AyVCCCBatchAggregation coverEvidence aggregateChecker publicResult ->
    (coverEvidence -> aggregateChecker -> unsatFact) ->
    unsatFact :=
  fun aggregation sound =>
    sound
      (ay_vccc_batch_aggregation_cover coverEvidence aggregateChecker
        publicResult aggregation)
      (ay_vccc_batch_aggregation_checker coverEvidence aggregateChecker
        publicResult aggregation)

theorem ay_vccc_incomplete_cover_no_claim
    (incompleteCover auditDigest diagnostic : Prop) :
    incompleteCover -> auditDigest -> diagnostic ->
    AyVCCCNoClaim incompleteCover auditDigest diagnostic :=
  ay_vccc_no_claim_intro incompleteCover auditDigest diagnostic

theorem ay_vccc_no_claim_cube_no_claim
    (noClaimCube auditDigest diagnostic : Prop) :
    noClaimCube -> auditDigest -> diagnostic ->
    AyVCCCNoClaim noClaimCube auditDigest diagnostic :=
  ay_vccc_no_claim_intro noClaimCube auditDigest diagnostic

theorem ay_vccc_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVCCCNoClaim reason auditDigest diagnostic ->
    AyVCCCPublicResult satFact unsatFact
      (AyVCCCNoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vccc_disj_right satFact
      (AyVCCCDisj unsatFact
        (AyVCCCNoClaim reason auditDigest diagnostic))
      (ay_vccc_disj_right unsatFact
        (AyVCCCNoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vccc_incomplete_or_no_claim_recompute
    (incompleteCover noClaimCube auditDigest diagnostic recompute : Prop) :
    AyVCCCDisj incompleteCover noClaimCube ->
    auditDigest -> diagnostic ->
    (incompleteCover ->
      AyVCCCRecomputeObligation incompleteCover auditDigest diagnostic ->
      recompute) ->
    (noClaimCube ->
      AyVCCCRecomputeObligation noClaimCube auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onIncomplete onNoClaim =>
    failure recompute
      (fun incompleteProof =>
        onIncomplete incompleteProof
          (ay_vccc_recompute_intro incompleteCover auditDigest diagnostic
            incompleteProof auditProof diagnosticProof))
      (fun noClaimProof =>
        onNoClaim noClaimProof
          (ay_vccc_recompute_intro noClaimCube auditDigest diagnostic
            noClaimProof auditProof diagnosticProof))
