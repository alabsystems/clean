-- SAT-COMP validator competition-bundle soundness core.
--
-- A public competition bundle may expose SAT/UNSAT only when checker result,
-- artifact membership, archive digest, solver run id, and preprocessing
-- evidence agree.  Missing artifacts, wrong run ids, stale archives, and
-- mismatched proof/model evidence are no-claim recomputation cases.

def AyVCBSConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVCBSDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVCBSEquisat (before after : Prop) : Prop :=
  AyVCBSConj (before -> after) (after -> before)

def AyVCBSPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVCBSDisj satFact (AyVCBSDisj unsatFact noClaim)

def AyVCBSBundleEvidence
    (checkerAccepted artifactMember archiveDigest runIdMatch
      preprocessChain : Prop) : Prop :=
  AyVCBSConj checkerAccepted
    (AyVCBSConj artifactMember
      (AyVCBSConj archiveDigest
        (AyVCBSConj runIdMatch preprocessChain)))

def AyVCBSCompetitionBundle
    (solverRunId publicOutput bundleEvidence publicArtifact : Prop) :
    Prop :=
  AyVCBSConj solverRunId
    (AyVCBSConj publicOutput
      (AyVCBSConj bundleEvidence publicArtifact))

def AyVCBSEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVCBSConj exitCode
    (AyVCBSConj artifacts
      (AyVCBSConj checkerDecision
        (AyVCBSConj auditDigest diagnostic)))

def AyVCBSMembership (leafHash root entry : Prop) : Prop :=
  AyVCBSConj leafHash (AyVCBSConj root entry)

def AyVCBSFailure (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCBSConj reason (AyVCBSConj auditDigest diagnostic)

def AyVCBSRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCBSConj reason (AyVCBSConj auditDigest diagnostic)

def AyVCBSNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVCBSConj reason (AyVCBSConj auditDigest diagnostic)

def AyVCBSModel (formula assignment : Prop) : Prop :=
  AyVCBSConj formula assignment

def AyVCBSUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVCBSVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVCBSModel original visibleAssignment

def AyVCBSPreprocessArtifact (original solver : Prop) : Prop :=
  AyVCBSEquisat original solver

def AyVCBSReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vcbs_conj_intro (left right : Prop) :
    left -> right -> AyVCBSConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vcbs_conj_left (left right : Prop) :
    AyVCBSConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vcbs_conj_right (left right : Prop) :
    AyVCBSConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vcbs_disj_right (left right : Prop) :
    right -> AyVCBSDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vcbs_equisat_forward (before after : Prop) :
    AyVCBSEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vcbs_equisat_backward (before after : Prop) :
    AyVCBSEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vcbs_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVCBSModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vcbs_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vcbs_model_formula (formula assignment : Prop) :
    AyVCBSModel formula assignment -> formula :=
  fun model => ay_vcbs_conj_left formula assignment model

theorem ay_vcbs_model_assignment (formula assignment : Prop) :
    AyVCBSModel formula assignment -> assignment :=
  fun model => ay_vcbs_conj_right formula assignment model

theorem ay_vcbs_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVCBSEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vcbs_conj_intro exitCode
      (AyVCBSConj artifacts
        (AyVCBSConj checkerDecision (AyVCBSConj auditDigest diagnostic)))
      exitProof
      (ay_vcbs_conj_intro artifacts
        (AyVCBSConj checkerDecision (AyVCBSConj auditDigest diagnostic))
        artifactsProof
        (ay_vcbs_conj_intro checkerDecision
          (AyVCBSConj auditDigest diagnostic)
          checkerProof
          (ay_vcbs_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vcbs_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVCBSEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vcbs_conj_right exitCode
      (AyVCBSConj artifacts
        (AyVCBSConj checkerDecision (AyVCBSConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vcbs_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVCBSMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vcbs_conj_intro leafHash (AyVCBSConj root entry)
      leafProof
      (ay_vcbs_conj_intro root entry rootProof entryProof)

theorem ay_vcbs_membership_entry (leafHash root entry : Prop) :
    AyVCBSMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vcbs_conj_right leafHash (AyVCBSConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vcbs_bundle_evidence_intro
    (checkerAccepted artifactMember archiveDigest runIdMatch
      preprocessChain : Prop) :
    checkerAccepted -> artifactMember -> archiveDigest -> runIdMatch ->
    preprocessChain ->
    AyVCBSBundleEvidence checkerAccepted artifactMember archiveDigest
      runIdMatch preprocessChain :=
  fun checkerProof artifactProof archiveProof runProof preprocessProof =>
    ay_vcbs_conj_intro checkerAccepted
      (AyVCBSConj artifactMember
        (AyVCBSConj archiveDigest
          (AyVCBSConj runIdMatch preprocessChain)))
      checkerProof
      (ay_vcbs_conj_intro artifactMember
        (AyVCBSConj archiveDigest
          (AyVCBSConj runIdMatch preprocessChain))
        artifactProof
        (ay_vcbs_conj_intro archiveDigest
          (AyVCBSConj runIdMatch preprocessChain)
          archiveProof
          (ay_vcbs_conj_intro runIdMatch preprocessChain runProof
            preprocessProof)))

theorem ay_vcbs_bundle_evidence_checker
    (checkerAccepted artifactMember archiveDigest runIdMatch
      preprocessChain : Prop) :
    AyVCBSBundleEvidence checkerAccepted artifactMember archiveDigest
      runIdMatch preprocessChain ->
    checkerAccepted :=
  fun evidence =>
    ay_vcbs_conj_left checkerAccepted
      (AyVCBSConj artifactMember
        (AyVCBSConj archiveDigest
          (AyVCBSConj runIdMatch preprocessChain)))
      evidence

theorem ay_vcbs_bundle_evidence_artifact
    (checkerAccepted artifactMember archiveDigest runIdMatch
      preprocessChain : Prop) :
    AyVCBSBundleEvidence checkerAccepted artifactMember archiveDigest
      runIdMatch preprocessChain ->
    artifactMember :=
  fun evidence =>
    ay_vcbs_conj_right checkerAccepted
      (AyVCBSConj artifactMember
        (AyVCBSConj archiveDigest
          (AyVCBSConj runIdMatch preprocessChain)))
      evidence artifactMember (fun artifactProof _tail => artifactProof)

theorem ay_vcbs_bundle_evidence_archive
    (checkerAccepted artifactMember archiveDigest runIdMatch
      preprocessChain : Prop) :
    AyVCBSBundleEvidence checkerAccepted artifactMember archiveDigest
      runIdMatch preprocessChain ->
    archiveDigest :=
  fun evidence =>
    ay_vcbs_conj_right checkerAccepted
      (AyVCBSConj artifactMember
        (AyVCBSConj archiveDigest
          (AyVCBSConj runIdMatch preprocessChain)))
      evidence archiveDigest
      (fun _artifactProof tail =>
        tail archiveDigest (fun archiveProof _rest => archiveProof))

theorem ay_vcbs_bundle_evidence_run_id
    (checkerAccepted artifactMember archiveDigest runIdMatch
      preprocessChain : Prop) :
    AyVCBSBundleEvidence checkerAccepted artifactMember archiveDigest
      runIdMatch preprocessChain ->
    runIdMatch :=
  fun evidence =>
    ay_vcbs_conj_right checkerAccepted
      (AyVCBSConj artifactMember
        (AyVCBSConj archiveDigest
          (AyVCBSConj runIdMatch preprocessChain)))
      evidence runIdMatch
      (fun _artifactProof tail =>
        tail runIdMatch
          (fun _archiveProof rest =>
            rest runIdMatch (fun runProof _preprocessProof => runProof)))

theorem ay_vcbs_bundle_evidence_preprocess
    (checkerAccepted artifactMember archiveDigest runIdMatch
      preprocessChain : Prop) :
    AyVCBSBundleEvidence checkerAccepted artifactMember archiveDigest
      runIdMatch preprocessChain ->
    preprocessChain :=
  fun evidence =>
    ay_vcbs_conj_right checkerAccepted
      (AyVCBSConj artifactMember
        (AyVCBSConj archiveDigest
          (AyVCBSConj runIdMatch preprocessChain)))
      evidence preprocessChain
      (fun _artifactProof tail =>
        tail preprocessChain
          (fun _archiveProof rest =>
            rest preprocessChain
              (fun _runProof preprocessProof => preprocessProof)))

theorem ay_vcbs_competition_bundle_intro
    (solverRunId publicOutput bundleEvidence publicArtifact : Prop) :
    solverRunId -> publicOutput -> bundleEvidence -> publicArtifact ->
    AyVCBSCompetitionBundle solverRunId publicOutput bundleEvidence
      publicArtifact :=
  fun runProof outputProof evidenceProof artifactProof =>
    ay_vcbs_conj_intro solverRunId
      (AyVCBSConj publicOutput
        (AyVCBSConj bundleEvidence publicArtifact))
      runProof
      (ay_vcbs_conj_intro publicOutput
        (AyVCBSConj bundleEvidence publicArtifact)
        outputProof
        (ay_vcbs_conj_intro bundleEvidence publicArtifact evidenceProof
          artifactProof))

theorem ay_vcbs_competition_bundle_run
    (solverRunId publicOutput bundleEvidence publicArtifact : Prop) :
    AyVCBSCompetitionBundle solverRunId publicOutput bundleEvidence
      publicArtifact ->
    solverRunId :=
  fun bundle =>
    ay_vcbs_conj_left solverRunId
      (AyVCBSConj publicOutput
        (AyVCBSConj bundleEvidence publicArtifact))
      bundle

theorem ay_vcbs_competition_bundle_output
    (solverRunId publicOutput bundleEvidence publicArtifact : Prop) :
    AyVCBSCompetitionBundle solverRunId publicOutput bundleEvidence
      publicArtifact ->
    publicOutput :=
  fun bundle =>
    ay_vcbs_conj_right solverRunId
      (AyVCBSConj publicOutput
        (AyVCBSConj bundleEvidence publicArtifact))
      bundle publicOutput (fun outputProof _tail => outputProof)

theorem ay_vcbs_competition_bundle_evidence
    (solverRunId publicOutput bundleEvidence publicArtifact : Prop) :
    AyVCBSCompetitionBundle solverRunId publicOutput bundleEvidence
      publicArtifact ->
    bundleEvidence :=
  fun bundle =>
    ay_vcbs_conj_right solverRunId
      (AyVCBSConj publicOutput
        (AyVCBSConj bundleEvidence publicArtifact))
      bundle bundleEvidence
      (fun _outputProof tail =>
        tail bundleEvidence (fun evidenceProof _artifactProof =>
          evidenceProof))

theorem ay_vcbs_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCBSNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vcbs_conj_intro reason (AyVCBSConj auditDigest diagnostic)
      reasonProof
      (ay_vcbs_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vcbs_failure_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCBSFailure reason auditDigest diagnostic :=
  ay_vcbs_no_claim_intro reason auditDigest diagnostic

theorem ay_vcbs_failure_no_claim
    (reason auditDigest diagnostic : Prop) :
    AyVCBSFailure reason auditDigest diagnostic ->
    AyVCBSNoClaim reason auditDigest diagnostic :=
  fun failure => failure

theorem ay_vcbs_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVCBSRecomputeObligation reason auditDigest diagnostic :=
  ay_vcbs_no_claim_intro reason auditDigest diagnostic

theorem ay_vcbs_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVCBSPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVCBSModel solver internalAssignment ->
    AyVCBSVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vcbs_model_intro original visibleAssignment
      (ay_vcbs_equisat_backward original solver preprocess
        (ay_vcbs_model_formula solver internalAssignment model))
      (decode (ay_vcbs_model_assignment solver internalAssignment model))

theorem ay_vcbs_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVCBSPreprocessArtifact original solver ->
    AyVCBSUnsat solver ->
    AyVCBSUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vcbs_equisat_forward original solver preprocess originalProof)

theorem ay_vcbs_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVCBSPreprocessArtifact original solver ->
    AyVCBSReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVCBSUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vcbs_equisat_forward original solver preprocess originalProof))

theorem ay_vcbs_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVCBSPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVCBSModel solver internalAssignment) ->
    AyVCBSMembership leafHash root
      (AyVCBSEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVCBSVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vcbs_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vcbs_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vcbs_membership_entry leafHash root
            (AyVCBSEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vcbs_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVCBSPreprocessArtifact original solver ->
    AyVCBSReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVCBSMembership leafHash root
      (AyVCBSEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVCBSUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vcbs_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vcbs_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vcbs_membership_entry leafHash root
            (AyVCBSEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vcbs_consistent_bundle_public_sound
    (solverRunId publicOutput bundleEvidence publicArtifact
      satFact unsatFact noClaim : Prop) :
    AyVCBSCompetitionBundle solverRunId publicOutput bundleEvidence
      publicArtifact ->
    (solverRunId -> publicOutput -> bundleEvidence ->
      AyVCBSPublicResult satFact unsatFact noClaim) ->
    AyVCBSPublicResult satFact unsatFact noClaim :=
  fun bundle sound =>
    sound
      (ay_vcbs_competition_bundle_run solverRunId publicOutput
        bundleEvidence publicArtifact bundle)
      (ay_vcbs_competition_bundle_output solverRunId publicOutput
        bundleEvidence publicArtifact bundle)
      (ay_vcbs_competition_bundle_evidence solverRunId publicOutput
        bundleEvidence publicArtifact bundle)

theorem ay_vcbs_consistent_bundle_preserves_sat
    (solverRunId publicOutput bundleEvidence publicArtifact satFact :
      Prop) :
    AyVCBSCompetitionBundle solverRunId publicOutput bundleEvidence
      publicArtifact ->
    (publicOutput -> bundleEvidence -> satFact) ->
    satFact :=
  fun bundle sound =>
    sound
      (ay_vcbs_competition_bundle_output solverRunId publicOutput
        bundleEvidence publicArtifact bundle)
      (ay_vcbs_competition_bundle_evidence solverRunId publicOutput
        bundleEvidence publicArtifact bundle)

theorem ay_vcbs_consistent_bundle_preserves_unsat
    (solverRunId publicOutput bundleEvidence publicArtifact unsatFact :
      Prop) :
    AyVCBSCompetitionBundle solverRunId publicOutput bundleEvidence
      publicArtifact ->
    (publicOutput -> bundleEvidence -> unsatFact) ->
    unsatFact :=
  fun bundle sound =>
    sound
      (ay_vcbs_competition_bundle_output solverRunId publicOutput
        bundleEvidence publicArtifact bundle)
      (ay_vcbs_competition_bundle_evidence solverRunId publicOutput
        bundleEvidence publicArtifact bundle)

theorem ay_vcbs_missing_artifact_no_claim
    (missingArtifact auditDigest diagnostic : Prop) :
    missingArtifact -> auditDigest -> diagnostic ->
    AyVCBSNoClaim missingArtifact auditDigest diagnostic :=
  ay_vcbs_no_claim_intro missingArtifact auditDigest diagnostic

theorem ay_vcbs_wrong_run_id_no_claim
    (wrongRunId auditDigest diagnostic : Prop) :
    wrongRunId -> auditDigest -> diagnostic ->
    AyVCBSNoClaim wrongRunId auditDigest diagnostic :=
  ay_vcbs_no_claim_intro wrongRunId auditDigest diagnostic

theorem ay_vcbs_stale_archive_no_claim
    (staleArchive auditDigest diagnostic : Prop) :
    staleArchive -> auditDigest -> diagnostic ->
    AyVCBSNoClaim staleArchive auditDigest diagnostic :=
  ay_vcbs_no_claim_intro staleArchive auditDigest diagnostic

theorem ay_vcbs_mismatched_proof_or_model_no_claim
    (mismatch auditDigest diagnostic : Prop) :
    mismatch -> auditDigest -> diagnostic ->
    AyVCBSNoClaim mismatch auditDigest diagnostic :=
  ay_vcbs_no_claim_intro mismatch auditDigest diagnostic

theorem ay_vcbs_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVCBSFailure reason auditDigest diagnostic ->
    AyVCBSPublicResult satFact unsatFact
      (AyVCBSNoClaim reason auditDigest diagnostic) :=
  fun failure =>
    ay_vcbs_disj_right satFact
      (AyVCBSDisj unsatFact
        (AyVCBSNoClaim reason auditDigest diagnostic))
      (ay_vcbs_disj_right unsatFact
        (AyVCBSNoClaim reason auditDigest diagnostic)
        (ay_vcbs_failure_no_claim reason auditDigest diagnostic failure))

theorem ay_vcbs_failure_recompute
    (reason auditDigest diagnostic : Prop) :
    AyVCBSFailure reason auditDigest diagnostic ->
    AyVCBSRecomputeObligation reason auditDigest diagnostic :=
  fun failure => failure

theorem ay_vcbs_any_bundle_failure_recompute
    (missingArtifact wrongRunId staleArchive mismatch auditDigest diagnostic
      recompute : Prop) :
    AyVCBSDisj missingArtifact
      (AyVCBSDisj wrongRunId (AyVCBSDisj staleArchive mismatch)) ->
    auditDigest -> diagnostic ->
    (missingArtifact ->
      AyVCBSRecomputeObligation missingArtifact auditDigest diagnostic ->
      recompute) ->
    (wrongRunId ->
      AyVCBSRecomputeObligation wrongRunId auditDigest diagnostic ->
      recompute) ->
    (staleArchive ->
      AyVCBSRecomputeObligation staleArchive auditDigest diagnostic ->
      recompute) ->
    (mismatch ->
      AyVCBSRecomputeObligation mismatch auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onMissing onRun onStale
      onMismatch =>
    failure recompute
      (fun missingProof =>
        onMissing missingProof
          (ay_vcbs_recompute_intro missingArtifact auditDigest diagnostic
            missingProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun runProof =>
            onRun runProof
              (ay_vcbs_recompute_intro wrongRunId auditDigest diagnostic
                runProof auditProof diagnosticProof))
          (fun tail2 =>
            tail2 recompute
              (fun staleProof =>
                onStale staleProof
                  (ay_vcbs_recompute_intro staleArchive auditDigest
                    diagnostic staleProof auditProof diagnosticProof))
              (fun mismatchProof =>
                onMismatch mismatchProof
                  (ay_vcbs_recompute_intro mismatch auditDigest diagnostic
                    mismatchProof auditProof diagnosticProof)))
