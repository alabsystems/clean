-- SAT-COMP validator cube-batch result-index soundness core.
--
-- A batch index of cube SAT/UNSAT/no-claim results is public-result sound only
-- when cube coverage, cube frame identity, artifact digest, checker replay,
-- and preprocessing-delta evidence agree.  Missing or mismatched cube entries
-- become no-claim recomputation obligations.

def AyVCBIConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVCBIDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVCBIEquisat (before after : Prop) : Prop :=
  AyVCBIConj (before -> after) (after -> before)

def AyVCBIPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVCBIDisj satFact (AyVCBIDisj unsatFact noClaim)

def AyVCBICubeEvidence
    (cubeCoverage cubeFrame artifactDigest checkerReplay preprocessDelta :
      Prop) : Prop :=
  AyVCBIConj cubeCoverage
    (AyVCBIConj cubeFrame
      (AyVCBIConj artifactDigest
        (AyVCBIConj checkerReplay preprocessDelta)))

def AyVCBIBatchIndex
    (batchId cubeEntries cubeEvidence batchDigest : Prop) : Prop :=
  AyVCBIConj batchId
    (AyVCBIConj cubeEntries
      (AyVCBIConj cubeEvidence batchDigest))

def AyVCBICubeResult
    (cubeId publicLabel resultArtifact cubeDigest : Prop) : Prop :=
  AyVCBIConj cubeId
    (AyVCBIConj publicLabel
      (AyVCBIConj resultArtifact cubeDigest))

def AyVCBIBatchReplay
    (batchIndex cubeResult replayTrace publicResult : Prop) : Prop :=
  AyVCBIConj batchIndex
    (AyVCBIConj cubeResult
      (AyVCBIConj replayTrace publicResult))

def AyVCBIEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVCBIConj exitCode
    (AyVCBIConj artifacts
      (AyVCBIConj checkerDecision
        (AyVCBIConj auditDigest diagnostic)))

def AyVCBIMembership (leafHash root entry : Prop) : Prop :=
  AyVCBIConj leafHash (AyVCBIConj root entry)

def AyVCBINoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCBIConj reason (AyVCBIConj auditDigest diagnostic)

def AyVCBIRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCBIConj reason (AyVCBIConj auditDigest diagnostic)

def AyVCBIModel (formula assignment : Prop) : Prop :=
  AyVCBIConj formula assignment

def AyVCBIUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVCBIVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVCBIModel original visibleAssignment

def AyVCBIPreprocessArtifact (original solver : Prop) : Prop :=
  AyVCBIEquisat original solver

def AyVCBIReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vcbi_conj_intro (left right : Prop) :
    left -> right -> AyVCBIConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcbi_conj_left (left right : Prop) :
    AyVCBIConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcbi_conj_right (left right : Prop) :
    AyVCBIConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcbi_disj_right (left right : Prop) :
    right -> AyVCBIDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcbi_equisat_forward (before after : Prop) :
    AyVCBIEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vcbi_equisat_backward (before after : Prop) :
    AyVCBIEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vcbi_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVCBIModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vcbi_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vcbi_model_formula (formula assignment : Prop) :
    AyVCBIModel formula assignment -> formula :=
  fun model => ay_vcbi_conj_left formula assignment model

theorem ay_vcbi_model_assignment (formula assignment : Prop) :
    AyVCBIModel formula assignment -> assignment :=
  fun model => ay_vcbi_conj_right formula assignment model

theorem ay_vcbi_cube_evidence_intro
    (cubeCoverage cubeFrame artifactDigest checkerReplay preprocessDelta :
      Prop) :
    cubeCoverage -> cubeFrame -> artifactDigest -> checkerReplay ->
    preprocessDelta ->
    AyVCBICubeEvidence cubeCoverage cubeFrame artifactDigest checkerReplay
      preprocessDelta :=
  fun coverageProof frameProof digestProof replayProof deltaProof =>
    ay_vcbi_conj_intro cubeCoverage
      (AyVCBIConj cubeFrame
        (AyVCBIConj artifactDigest
          (AyVCBIConj checkerReplay preprocessDelta)))
      coverageProof
      (ay_vcbi_conj_intro cubeFrame
        (AyVCBIConj artifactDigest
          (AyVCBIConj checkerReplay preprocessDelta))
        frameProof
        (ay_vcbi_conj_intro artifactDigest
          (AyVCBIConj checkerReplay preprocessDelta)
          digestProof
          (ay_vcbi_conj_intro checkerReplay preprocessDelta replayProof
            deltaProof)))

theorem ay_vcbi_cube_evidence_coverage
    (cubeCoverage cubeFrame artifactDigest checkerReplay preprocessDelta :
      Prop) :
    AyVCBICubeEvidence cubeCoverage cubeFrame artifactDigest checkerReplay
      preprocessDelta ->
    cubeCoverage :=
  fun evidence =>
    ay_vcbi_conj_left cubeCoverage
      (AyVCBIConj cubeFrame
        (AyVCBIConj artifactDigest
          (AyVCBIConj checkerReplay preprocessDelta)))
      evidence

theorem ay_vcbi_cube_evidence_frame
    (cubeCoverage cubeFrame artifactDigest checkerReplay preprocessDelta :
      Prop) :
    AyVCBICubeEvidence cubeCoverage cubeFrame artifactDigest checkerReplay
      preprocessDelta ->
    cubeFrame :=
  fun evidence =>
    ay_vcbi_conj_right cubeCoverage
      (AyVCBIConj cubeFrame
        (AyVCBIConj artifactDigest
          (AyVCBIConj checkerReplay preprocessDelta)))
      evidence cubeFrame (fun frameProof _tail => frameProof)

theorem ay_vcbi_cube_evidence_replay
    (cubeCoverage cubeFrame artifactDigest checkerReplay preprocessDelta :
      Prop) :
    AyVCBICubeEvidence cubeCoverage cubeFrame artifactDigest checkerReplay
      preprocessDelta ->
    checkerReplay :=
  fun evidence =>
    ay_vcbi_conj_right cubeCoverage
      (AyVCBIConj cubeFrame
        (AyVCBIConj artifactDigest
          (AyVCBIConj checkerReplay preprocessDelta)))
      evidence checkerReplay
      (fun _frameProof tail =>
        tail checkerReplay
          (fun _digestProof replayTail =>
            replayTail checkerReplay
              (fun replayProof _deltaProof => replayProof)))

theorem ay_vcbi_cube_evidence_delta
    (cubeCoverage cubeFrame artifactDigest checkerReplay preprocessDelta :
      Prop) :
    AyVCBICubeEvidence cubeCoverage cubeFrame artifactDigest checkerReplay
      preprocessDelta ->
    preprocessDelta :=
  fun evidence =>
    ay_vcbi_conj_right cubeCoverage
      (AyVCBIConj cubeFrame
        (AyVCBIConj artifactDigest
          (AyVCBIConj checkerReplay preprocessDelta)))
      evidence preprocessDelta
      (fun _frameProof tail =>
        tail preprocessDelta
          (fun _digestProof replayTail =>
            replayTail preprocessDelta
              (fun _replayProof deltaProof => deltaProof)))

theorem ay_vcbi_batch_index_intro
    (batchId cubeEntries cubeEvidence batchDigest : Prop) :
    batchId -> cubeEntries -> cubeEvidence -> batchDigest ->
    AyVCBIBatchIndex batchId cubeEntries cubeEvidence batchDigest :=
  fun batchProof entriesProof evidenceProof digestProof =>
    ay_vcbi_conj_intro batchId
      (AyVCBIConj cubeEntries
        (AyVCBIConj cubeEvidence batchDigest))
      batchProof
      (ay_vcbi_conj_intro cubeEntries
        (AyVCBIConj cubeEvidence batchDigest)
        entriesProof
        (ay_vcbi_conj_intro cubeEvidence batchDigest evidenceProof
          digestProof))

theorem ay_vcbi_batch_index_evidence
    (batchId cubeEntries cubeEvidence batchDigest : Prop) :
    AyVCBIBatchIndex batchId cubeEntries cubeEvidence batchDigest ->
    cubeEvidence :=
  fun index =>
    ay_vcbi_conj_right batchId
      (AyVCBIConj cubeEntries
        (AyVCBIConj cubeEvidence batchDigest))
      index cubeEvidence
      (fun _entriesProof tail =>
        tail cubeEvidence (fun evidenceProof _digestProof =>
          evidenceProof))

theorem ay_vcbi_cube_result_intro
    (cubeId publicLabel resultArtifact cubeDigest : Prop) :
    cubeId -> publicLabel -> resultArtifact -> cubeDigest ->
    AyVCBICubeResult cubeId publicLabel resultArtifact cubeDigest :=
  fun cubeProof labelProof artifactProof digestProof =>
    ay_vcbi_conj_intro cubeId
      (AyVCBIConj publicLabel
        (AyVCBIConj resultArtifact cubeDigest))
      cubeProof
      (ay_vcbi_conj_intro publicLabel
        (AyVCBIConj resultArtifact cubeDigest)
        labelProof
        (ay_vcbi_conj_intro resultArtifact cubeDigest artifactProof
          digestProof))

theorem ay_vcbi_batch_replay_intro
    (batchIndex cubeResult replayTrace publicResult : Prop) :
    batchIndex -> cubeResult -> replayTrace -> publicResult ->
    AyVCBIBatchReplay batchIndex cubeResult replayTrace publicResult :=
  fun indexProof resultProof traceProof publicProof =>
    ay_vcbi_conj_intro batchIndex
      (AyVCBIConj cubeResult
        (AyVCBIConj replayTrace publicResult))
      indexProof
      (ay_vcbi_conj_intro cubeResult
        (AyVCBIConj replayTrace publicResult)
        resultProof
        (ay_vcbi_conj_intro replayTrace publicResult traceProof
          publicProof))

theorem ay_vcbi_batch_replay_index
    (batchIndex cubeResult replayTrace publicResult : Prop) :
    AyVCBIBatchReplay batchIndex cubeResult replayTrace publicResult ->
    batchIndex :=
  fun replay =>
    ay_vcbi_conj_left batchIndex
      (AyVCBIConj cubeResult
        (AyVCBIConj replayTrace publicResult))
      replay

theorem ay_vcbi_batch_replay_result
    (batchIndex cubeResult replayTrace publicResult : Prop) :
    AyVCBIBatchReplay batchIndex cubeResult replayTrace publicResult ->
    cubeResult :=
  fun replay =>
    ay_vcbi_conj_right batchIndex
      (AyVCBIConj cubeResult
        (AyVCBIConj replayTrace publicResult))
      replay cubeResult (fun resultProof _tail => resultProof)

theorem ay_vcbi_batch_replay_public
    (batchIndex cubeResult replayTrace publicResult : Prop) :
    AyVCBIBatchReplay batchIndex cubeResult replayTrace publicResult ->
    publicResult :=
  fun replay =>
    ay_vcbi_conj_right batchIndex
      (AyVCBIConj cubeResult
        (AyVCBIConj replayTrace publicResult))
      replay publicResult
      (fun _resultProof tail =>
        tail publicResult (fun _traceProof publicProof => publicProof))

theorem ay_vcbi_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVCBIEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vcbi_conj_intro exitCode
      (AyVCBIConj artifacts
        (AyVCBIConj checkerDecision (AyVCBIConj auditDigest diagnostic)))
      exitProof
      (ay_vcbi_conj_intro artifacts
        (AyVCBIConj checkerDecision (AyVCBIConj auditDigest diagnostic))
        artifactsProof
        (ay_vcbi_conj_intro checkerDecision
          (AyVCBIConj auditDigest diagnostic)
          checkerProof
          (ay_vcbi_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vcbi_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVCBIEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vcbi_conj_right exitCode
      (AyVCBIConj artifacts
        (AyVCBIConj checkerDecision (AyVCBIConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vcbi_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVCBIMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vcbi_conj_intro leafHash (AyVCBIConj root entry)
      leafProof
      (ay_vcbi_conj_intro root entry rootProof entryProof)

theorem ay_vcbi_membership_entry (leafHash root entry : Prop) :
    AyVCBIMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vcbi_conj_right leafHash (AyVCBIConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vcbi_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCBINoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vcbi_conj_intro reason (AyVCBIConj auditDigest diagnostic)
      reasonProof
      (ay_vcbi_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vcbi_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCBIRecomputeObligation reason auditDigest diagnostic :=
  ay_vcbi_no_claim_intro reason auditDigest diagnostic

theorem ay_vcbi_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVCBIPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVCBIModel solver internalAssignment ->
    AyVCBIVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vcbi_model_intro original visibleAssignment
      (ay_vcbi_equisat_backward original solver preprocess
        (ay_vcbi_model_formula solver internalAssignment model))
      (decode (ay_vcbi_model_assignment solver internalAssignment model))

theorem ay_vcbi_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVCBIPreprocessArtifact original solver ->
    AyVCBIUnsat solver ->
    AyVCBIUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vcbi_equisat_forward original solver preprocess originalProof)

theorem ay_vcbi_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVCBIPreprocessArtifact original solver ->
    AyVCBIReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVCBIUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vcbi_equisat_forward original solver preprocess originalProof))

theorem ay_vcbi_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVCBIPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVCBIModel solver internalAssignment) ->
    AyVCBIMembership leafHash root
      (AyVCBIEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVCBIVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vcbi_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vcbi_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vcbi_membership_entry leafHash root
            (AyVCBIEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vcbi_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVCBIPreprocessArtifact original solver ->
    AyVCBIReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVCBIMembership leafHash root
      (AyVCBIEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVCBIUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vcbi_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vcbi_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vcbi_membership_entry leafHash root
            (AyVCBIEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vcbi_batch_public_sound
    (batchIndex cubeResult replayTrace publicResult
      satFact unsatFact noClaim : Prop) :
    AyVCBIBatchReplay batchIndex cubeResult replayTrace publicResult ->
    (batchIndex -> cubeResult -> publicResult ->
      AyVCBIPublicResult satFact unsatFact noClaim) ->
    AyVCBIPublicResult satFact unsatFact noClaim :=
  fun replay sound =>
    sound
      (ay_vcbi_batch_replay_index batchIndex cubeResult replayTrace
        publicResult replay)
      (ay_vcbi_batch_replay_result batchIndex cubeResult replayTrace
        publicResult replay)
      (ay_vcbi_batch_replay_public batchIndex cubeResult replayTrace
        publicResult replay)

theorem ay_vcbi_batch_preserves_sat
    (batchIndex cubeResult replayTrace publicResult satFact : Prop) :
    AyVCBIBatchReplay batchIndex cubeResult replayTrace publicResult ->
    (batchIndex -> publicResult -> satFact) ->
    satFact :=
  fun replay sound =>
    sound
      (ay_vcbi_batch_replay_index batchIndex cubeResult replayTrace
        publicResult replay)
      (ay_vcbi_batch_replay_public batchIndex cubeResult replayTrace
        publicResult replay)

theorem ay_vcbi_batch_preserves_unsat
    (batchIndex cubeResult replayTrace publicResult unsatFact : Prop) :
    AyVCBIBatchReplay batchIndex cubeResult replayTrace publicResult ->
    (batchIndex -> publicResult -> unsatFact) ->
    unsatFact :=
  fun replay sound =>
    sound
      (ay_vcbi_batch_replay_index batchIndex cubeResult replayTrace
        publicResult replay)
      (ay_vcbi_batch_replay_public batchIndex cubeResult replayTrace
        publicResult replay)

theorem ay_vcbi_missing_cube_result_no_claim
    (missingCubeResult auditDigest diagnostic : Prop) :
    missingCubeResult -> auditDigest -> diagnostic ->
    AyVCBINoClaim missingCubeResult auditDigest diagnostic :=
  ay_vcbi_no_claim_intro missingCubeResult auditDigest diagnostic

theorem ay_vcbi_mismatched_cube_entry_no_claim
    (mismatchedCubeEntry auditDigest diagnostic : Prop) :
    mismatchedCubeEntry -> auditDigest -> diagnostic ->
    AyVCBINoClaim mismatchedCubeEntry auditDigest diagnostic :=
  ay_vcbi_no_claim_intro mismatchedCubeEntry auditDigest diagnostic

theorem ay_vcbi_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVCBINoClaim reason auditDigest diagnostic ->
    AyVCBIPublicResult satFact unsatFact
      (AyVCBINoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vcbi_disj_right satFact
      (AyVCBIDisj unsatFact
        (AyVCBINoClaim reason auditDigest diagnostic))
      (ay_vcbi_disj_right unsatFact
        (AyVCBINoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vcbi_missing_or_mismatched_recompute
    (missingCubeResult mismatchedCubeEntry auditDigest diagnostic recompute :
      Prop) :
    AyVCBIDisj missingCubeResult mismatchedCubeEntry ->
    auditDigest -> diagnostic ->
    (missingCubeResult ->
      AyVCBIRecomputeObligation missingCubeResult auditDigest diagnostic ->
      recompute) ->
    (mismatchedCubeEntry ->
      AyVCBIRecomputeObligation mismatchedCubeEntry auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onMissing onMismatch =>
    failure recompute
      (fun missingProof =>
        onMissing missingProof
          (ay_vcbi_recompute_intro missingCubeResult auditDigest diagnostic
            missingProof auditProof diagnosticProof))
      (fun mismatchProof =>
        onMismatch mismatchProof
          (ay_vcbi_recompute_intro mismatchedCubeEntry auditDigest
            diagnostic mismatchProof auditProof diagnosticProof))
