-- SAT-COMP validator cube-cover no-claim aggregation core.
--
-- Cube-cover aggregation may publish SAT/UNSAT only from a complete cover
-- whose cubes replay in the same cube frame.  Any no-claim cube, missing cube,
-- frame mismatch, or rejected checker replay remains diagnostic no-claim data
-- and forces recomputation instead of a stale public SAT/UNSAT result.

def AyVCNAConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVCNADisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVCNAEquisat (before after : Prop) : Prop :=
  AyVCNAConj (before -> after) (after -> before)

def AyVCNAPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVCNADisj satFact (AyVCNADisj unsatFact noClaim)

def AyVCNACubeReplay
    (cubeFrame replayedEvidence checkerAccepted publicLabel : Prop) :
    Prop :=
  AyVCNAConj cubeFrame
    (AyVCNAConj replayedEvidence
      (AyVCNAConj checkerAccepted publicLabel))

def AyVCNACompleteCover
    (baseFormula coverComplete sameCubeFrame allCubeReplay : Prop) :
    Prop :=
  AyVCNAConj baseFormula
    (AyVCNAConj coverComplete
      (AyVCNAConj sameCubeFrame allCubeReplay))

def AyVCNAAggregate
    (completeCover aggregateChecker publicResult : Prop) : Prop :=
  AyVCNAConj completeCover
    (AyVCNAConj aggregateChecker publicResult)

def AyVCNAEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVCNAConj exitCode
    (AyVCNAConj artifacts
      (AyVCNAConj checkerDecision
        (AyVCNAConj auditDigest diagnostic)))

def AyVCNAMembership (leafHash root entry : Prop) : Prop :=
  AyVCNAConj leafHash (AyVCNAConj root entry)

def AyVCNANoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCNAConj reason (AyVCNAConj auditDigest diagnostic)

def AyVCNARecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCNAConj reason (AyVCNAConj auditDigest diagnostic)

def AyVCNAModel (formula assignment : Prop) : Prop :=
  AyVCNAConj formula assignment

def AyVCNAUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVCNAVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVCNAModel original visibleAssignment

def AyVCNAPreprocessArtifact (original solver : Prop) : Prop :=
  AyVCNAEquisat original solver

def AyVCNAReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vcna_conj_intro (left right : Prop) :
    left -> right -> AyVCNAConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcna_conj_left (left right : Prop) :
    AyVCNAConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcna_conj_right (left right : Prop) :
    AyVCNAConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcna_disj_right (left right : Prop) :
    right -> AyVCNADisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcna_equisat_forward (before after : Prop) :
    AyVCNAEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vcna_equisat_backward (before after : Prop) :
    AyVCNAEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vcna_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVCNAModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vcna_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vcna_model_formula (formula assignment : Prop) :
    AyVCNAModel formula assignment -> formula :=
  fun model => ay_vcna_conj_left formula assignment model

theorem ay_vcna_model_assignment (formula assignment : Prop) :
    AyVCNAModel formula assignment -> assignment :=
  fun model => ay_vcna_conj_right formula assignment model

theorem ay_vcna_cube_replay_intro
    (cubeFrame replayedEvidence checkerAccepted publicLabel : Prop) :
    cubeFrame -> replayedEvidence -> checkerAccepted -> publicLabel ->
    AyVCNACubeReplay cubeFrame replayedEvidence checkerAccepted
      publicLabel :=
  fun frameProof replayProof checkerProof labelProof =>
    ay_vcna_conj_intro cubeFrame
      (AyVCNAConj replayedEvidence
        (AyVCNAConj checkerAccepted publicLabel))
      frameProof
      (ay_vcna_conj_intro replayedEvidence
        (AyVCNAConj checkerAccepted publicLabel)
        replayProof
        (ay_vcna_conj_intro checkerAccepted publicLabel checkerProof
          labelProof))

theorem ay_vcna_cube_replay_frame
    (cubeFrame replayedEvidence checkerAccepted publicLabel : Prop) :
    AyVCNACubeReplay cubeFrame replayedEvidence checkerAccepted
      publicLabel ->
    cubeFrame :=
  fun replay =>
    ay_vcna_conj_left cubeFrame
      (AyVCNAConj replayedEvidence
        (AyVCNAConj checkerAccepted publicLabel))
      replay

theorem ay_vcna_cube_replay_checker
    (cubeFrame replayedEvidence checkerAccepted publicLabel : Prop) :
    AyVCNACubeReplay cubeFrame replayedEvidence checkerAccepted
      publicLabel ->
    checkerAccepted :=
  fun replay =>
    ay_vcna_conj_right cubeFrame
      (AyVCNAConj replayedEvidence
        (AyVCNAConj checkerAccepted publicLabel))
      replay checkerAccepted
      (fun _replayProof tail =>
        tail checkerAccepted (fun checkerProof _labelProof =>
          checkerProof))

theorem ay_vcna_complete_cover_intro
    (baseFormula coverComplete sameCubeFrame allCubeReplay : Prop) :
    baseFormula -> coverComplete -> sameCubeFrame -> allCubeReplay ->
    AyVCNACompleteCover baseFormula coverComplete sameCubeFrame
      allCubeReplay :=
  fun baseProof completeProof frameProof replayProof =>
    ay_vcna_conj_intro baseFormula
      (AyVCNAConj coverComplete
        (AyVCNAConj sameCubeFrame allCubeReplay))
      baseProof
      (ay_vcna_conj_intro coverComplete
        (AyVCNAConj sameCubeFrame allCubeReplay)
        completeProof
        (ay_vcna_conj_intro sameCubeFrame allCubeReplay frameProof
          replayProof))

theorem ay_vcna_complete_cover_complete
    (baseFormula coverComplete sameCubeFrame allCubeReplay : Prop) :
    AyVCNACompleteCover baseFormula coverComplete sameCubeFrame
      allCubeReplay ->
    coverComplete :=
  fun cover =>
    ay_vcna_conj_right baseFormula
      (AyVCNAConj coverComplete
        (AyVCNAConj sameCubeFrame allCubeReplay))
      cover coverComplete (fun completeProof _tail => completeProof)

theorem ay_vcna_complete_cover_frame
    (baseFormula coverComplete sameCubeFrame allCubeReplay : Prop) :
    AyVCNACompleteCover baseFormula coverComplete sameCubeFrame
      allCubeReplay ->
    sameCubeFrame :=
  fun cover =>
    ay_vcna_conj_right baseFormula
      (AyVCNAConj coverComplete
        (AyVCNAConj sameCubeFrame allCubeReplay))
      cover sameCubeFrame
      (fun _completeProof tail =>
        tail sameCubeFrame
          (fun frameProof _replayProof => frameProof))

theorem ay_vcna_complete_cover_replay
    (baseFormula coverComplete sameCubeFrame allCubeReplay : Prop) :
    AyVCNACompleteCover baseFormula coverComplete sameCubeFrame
      allCubeReplay ->
    allCubeReplay :=
  fun cover =>
    ay_vcna_conj_right baseFormula
      (AyVCNAConj coverComplete
        (AyVCNAConj sameCubeFrame allCubeReplay))
      cover allCubeReplay
      (fun _completeProof tail =>
        tail allCubeReplay
          (fun _frameProof replayProof => replayProof))

theorem ay_vcna_aggregate_intro
    (completeCover aggregateChecker publicResult : Prop) :
    completeCover -> aggregateChecker -> publicResult ->
    AyVCNAAggregate completeCover aggregateChecker publicResult :=
  fun coverProof checkerProof publicProof =>
    ay_vcna_conj_intro completeCover
      (AyVCNAConj aggregateChecker publicResult)
      coverProof
      (ay_vcna_conj_intro aggregateChecker publicResult checkerProof
        publicProof)

theorem ay_vcna_aggregate_cover
    (completeCover aggregateChecker publicResult : Prop) :
    AyVCNAAggregate completeCover aggregateChecker publicResult ->
    completeCover :=
  fun aggregate =>
    ay_vcna_conj_left completeCover
      (AyVCNAConj aggregateChecker publicResult) aggregate

theorem ay_vcna_aggregate_checker
    (completeCover aggregateChecker publicResult : Prop) :
    AyVCNAAggregate completeCover aggregateChecker publicResult ->
    aggregateChecker :=
  fun aggregate =>
    ay_vcna_conj_right completeCover
      (AyVCNAConj aggregateChecker publicResult)
      aggregate aggregateChecker
      (fun checkerProof _publicProof => checkerProof)

theorem ay_vcna_aggregate_public
    (completeCover aggregateChecker publicResult : Prop) :
    AyVCNAAggregate completeCover aggregateChecker publicResult ->
    publicResult :=
  fun aggregate =>
    ay_vcna_conj_right completeCover
      (AyVCNAConj aggregateChecker publicResult)
      aggregate publicResult
      (fun _checkerProof publicProof => publicProof)

theorem ay_vcna_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVCNAEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vcna_conj_intro exitCode
      (AyVCNAConj artifacts
        (AyVCNAConj checkerDecision (AyVCNAConj auditDigest diagnostic)))
      exitProof
      (ay_vcna_conj_intro artifacts
        (AyVCNAConj checkerDecision (AyVCNAConj auditDigest diagnostic))
        artifactsProof
        (ay_vcna_conj_intro checkerDecision
          (AyVCNAConj auditDigest diagnostic)
          checkerProof
          (ay_vcna_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vcna_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVCNAEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vcna_conj_right exitCode
      (AyVCNAConj artifacts
        (AyVCNAConj checkerDecision (AyVCNAConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vcna_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVCNAMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vcna_conj_intro leafHash (AyVCNAConj root entry)
      leafProof
      (ay_vcna_conj_intro root entry rootProof entryProof)

theorem ay_vcna_membership_entry (leafHash root entry : Prop) :
    AyVCNAMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vcna_conj_right leafHash (AyVCNAConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vcna_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCNANoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vcna_conj_intro reason (AyVCNAConj auditDigest diagnostic)
      reasonProof
      (ay_vcna_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vcna_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCNARecomputeObligation reason auditDigest diagnostic :=
  ay_vcna_no_claim_intro reason auditDigest diagnostic

theorem ay_vcna_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVCNAPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVCNAModel solver internalAssignment ->
    AyVCNAVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vcna_model_intro original visibleAssignment
      (ay_vcna_equisat_backward original solver preprocess
        (ay_vcna_model_formula solver internalAssignment model))
      (decode (ay_vcna_model_assignment solver internalAssignment model))

theorem ay_vcna_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVCNAPreprocessArtifact original solver ->
    AyVCNAUnsat solver ->
    AyVCNAUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vcna_equisat_forward original solver preprocess originalProof)

theorem ay_vcna_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVCNAPreprocessArtifact original solver ->
    AyVCNAReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVCNAUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vcna_equisat_forward original solver preprocess originalProof))

theorem ay_vcna_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVCNAPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVCNAModel solver internalAssignment) ->
    AyVCNAMembership leafHash root
      (AyVCNAEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVCNAVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vcna_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vcna_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vcna_membership_entry leafHash root
            (AyVCNAEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vcna_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVCNAPreprocessArtifact original solver ->
    AyVCNAReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVCNAMembership leafHash root
      (AyVCNAEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVCNAUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vcna_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vcna_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vcna_membership_entry leafHash root
            (AyVCNAEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vcna_complete_aggregate_public_sound
    (completeCover aggregateChecker publicResult satFact unsatFact
      noClaim : Prop) :
    AyVCNAAggregate completeCover aggregateChecker publicResult ->
    (completeCover -> aggregateChecker -> publicResult ->
      AyVCNAPublicResult satFact unsatFact noClaim) ->
    AyVCNAPublicResult satFact unsatFact noClaim :=
  fun aggregate sound =>
    sound
      (ay_vcna_aggregate_cover completeCover aggregateChecker publicResult
        aggregate)
      (ay_vcna_aggregate_checker completeCover aggregateChecker
        publicResult aggregate)
      (ay_vcna_aggregate_public completeCover aggregateChecker publicResult
        aggregate)

theorem ay_vcna_complete_aggregate_preserves_sat
    (completeCover aggregateChecker publicResult satFact : Prop) :
    AyVCNAAggregate completeCover aggregateChecker publicResult ->
    (completeCover -> aggregateChecker -> satFact) ->
    satFact :=
  fun aggregate sound =>
    sound
      (ay_vcna_aggregate_cover completeCover aggregateChecker publicResult
        aggregate)
      (ay_vcna_aggregate_checker completeCover aggregateChecker
        publicResult aggregate)

theorem ay_vcna_complete_aggregate_preserves_unsat
    (completeCover aggregateChecker publicResult unsatFact : Prop) :
    AyVCNAAggregate completeCover aggregateChecker publicResult ->
    (completeCover -> aggregateChecker -> unsatFact) ->
    unsatFact :=
  fun aggregate sound =>
    sound
      (ay_vcna_aggregate_cover completeCover aggregateChecker publicResult
        aggregate)
      (ay_vcna_aggregate_checker completeCover aggregateChecker
        publicResult aggregate)

theorem ay_vcna_no_claim_cube_no_claim
    (noClaimCube auditDigest diagnostic : Prop) :
    noClaimCube -> auditDigest -> diagnostic ->
    AyVCNANoClaim noClaimCube auditDigest diagnostic :=
  ay_vcna_no_claim_intro noClaimCube auditDigest diagnostic

theorem ay_vcna_missing_cube_no_claim
    (missingCube auditDigest diagnostic : Prop) :
    missingCube -> auditDigest -> diagnostic ->
    AyVCNANoClaim missingCube auditDigest diagnostic :=
  ay_vcna_no_claim_intro missingCube auditDigest diagnostic

theorem ay_vcna_mismatched_frame_no_claim
    (mismatchedFrame auditDigest diagnostic : Prop) :
    mismatchedFrame -> auditDigest -> diagnostic ->
    AyVCNANoClaim mismatchedFrame auditDigest diagnostic :=
  ay_vcna_no_claim_intro mismatchedFrame auditDigest diagnostic

theorem ay_vcna_rejected_replay_no_claim
    (rejectedReplay auditDigest diagnostic : Prop) :
    rejectedReplay -> auditDigest -> diagnostic ->
    AyVCNANoClaim rejectedReplay auditDigest diagnostic :=
  ay_vcna_no_claim_intro rejectedReplay auditDigest diagnostic

theorem ay_vcna_diagnostic_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVCNANoClaim reason auditDigest diagnostic ->
    AyVCNAPublicResult satFact unsatFact
      (AyVCNANoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vcna_disj_right satFact
      (AyVCNADisj unsatFact
        (AyVCNANoClaim reason auditDigest diagnostic))
      (ay_vcna_disj_right unsatFact
        (AyVCNANoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vcna_diagnostic_preserves_no_claim
    (reason auditDigest diagnostic noClaim : Prop) :
    AyVCNANoClaim reason auditDigest diagnostic ->
    (AyVCNANoClaim reason auditDigest diagnostic -> noClaim) ->
    noClaim :=
  fun diagnostic toNoClaim => toNoClaim diagnostic

theorem ay_vcna_bad_cube_recompute
    (noClaimCube missingCube mismatchedFrame rejectedReplay auditDigest
      diagnostic recompute : Prop) :
    AyVCNADisj noClaimCube
      (AyVCNADisj missingCube
        (AyVCNADisj mismatchedFrame rejectedReplay)) ->
    auditDigest -> diagnostic ->
    (noClaimCube ->
      AyVCNARecomputeObligation noClaimCube auditDigest diagnostic ->
      recompute) ->
    (missingCube ->
      AyVCNARecomputeObligation missingCube auditDigest diagnostic ->
      recompute) ->
    (mismatchedFrame ->
      AyVCNARecomputeObligation mismatchedFrame auditDigest diagnostic ->
      recompute) ->
    (rejectedReplay ->
      AyVCNARecomputeObligation rejectedReplay auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onNoClaim onMissing onFrame
      onRejected =>
    failure recompute
      (fun noClaimProof =>
        onNoClaim noClaimProof
          (ay_vcna_recompute_intro noClaimCube auditDigest diagnostic
            noClaimProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun missingProof =>
            onMissing missingProof
              (ay_vcna_recompute_intro missingCube auditDigest diagnostic
                missingProof auditProof diagnosticProof))
          (fun tail2 =>
            tail2 recompute
              (fun frameProof =>
                onFrame frameProof
                  (ay_vcna_recompute_intro mismatchedFrame auditDigest
                    diagnostic frameProof auditProof diagnosticProof))
              (fun rejectedProof =>
                onRejected rejectedProof
                  (ay_vcna_recompute_intro rejectedReplay auditDigest
                    diagnostic rejectedProof auditProof diagnosticProof)))
