-- SAT-COMP validator exit-code/public-result contract soundness core.
--
-- Competition-facing exit codes and public labels may expose SAT/UNSAT only
-- when the matching model/proof/checker evidence agrees with the run manifest.
-- Timeout, resource exhaustion, replay divergence, or artifact mismatch are
-- no-claim/non-answer labels.

def AyVECPConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVECPDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVECPEquisat (before after : Prop) : Prop :=
  AyVECPConj (before -> after) (after -> before)

def AyVECPPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVECPDisj satFact (AyVECPDisj unsatFact noClaim)

def AyVECPExitContract
    (exitCode publicLabel manifestAgreement checkerEvidence : Prop) :
    Prop :=
  AyVECPConj exitCode
    (AyVECPConj publicLabel
      (AyVECPConj manifestAgreement checkerEvidence))

def AyVECPRunManifest
    (runId formulaFingerprint preprocessChain artifactDigest : Prop) :
    Prop :=
  AyVECPConj runId
    (AyVECPConj formulaFingerprint
      (AyVECPConj preprocessChain artifactDigest))

def AyVECPModelEvidence
    (modelArtifact modelChecker manifestAgreement : Prop) : Prop :=
  AyVECPConj modelArtifact
    (AyVECPConj modelChecker manifestAgreement)

def AyVECPProofEvidence
    (proofArtifact proofChecker manifestAgreement : Prop) : Prop :=
  AyVECPConj proofArtifact
    (AyVECPConj proofChecker manifestAgreement)

def AyVECPNonAnswer (reason auditDigest diagnostic : Prop) : Prop :=
  AyVECPConj reason (AyVECPConj auditDigest diagnostic)

def AyVECPNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVECPConj reason (AyVECPConj auditDigest diagnostic)

def AyVECPRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVECPConj reason (AyVECPConj auditDigest diagnostic)

def AyVECPEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVECPConj exitCode
    (AyVECPConj artifacts
      (AyVECPConj checkerDecision
        (AyVECPConj auditDigest diagnostic)))

def AyVECPMembership (leafHash root entry : Prop) : Prop :=
  AyVECPConj leafHash (AyVECPConj root entry)

def AyVECPModel (formula assignment : Prop) : Prop :=
  AyVECPConj formula assignment

def AyVECPUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVECPVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVECPModel original visibleAssignment

def AyVECPPreprocessArtifact (original solver : Prop) : Prop :=
  AyVECPEquisat original solver

def AyVECPReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vecp_conj_intro (left right : Prop) :
    left -> right -> AyVECPConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vecp_conj_left (left right : Prop) :
    AyVECPConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vecp_conj_right (left right : Prop) :
    AyVECPConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vecp_disj_right (left right : Prop) :
    right -> AyVECPDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vecp_equisat_forward (before after : Prop) :
    AyVECPEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vecp_equisat_backward (before after : Prop) :
    AyVECPEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vecp_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVECPModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vecp_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vecp_model_formula (formula assignment : Prop) :
    AyVECPModel formula assignment -> formula :=
  fun model => ay_vecp_conj_left formula assignment model

theorem ay_vecp_model_assignment (formula assignment : Prop) :
    AyVECPModel formula assignment -> assignment :=
  fun model => ay_vecp_conj_right formula assignment model

theorem ay_vecp_exit_contract_intro
    (exitCode publicLabel manifestAgreement checkerEvidence : Prop) :
    exitCode -> publicLabel -> manifestAgreement -> checkerEvidence ->
    AyVECPExitContract exitCode publicLabel manifestAgreement
      checkerEvidence :=
  fun exitProof labelProof manifestProof checkerProof =>
    ay_vecp_conj_intro exitCode
      (AyVECPConj publicLabel
        (AyVECPConj manifestAgreement checkerEvidence))
      exitProof
      (ay_vecp_conj_intro publicLabel
        (AyVECPConj manifestAgreement checkerEvidence)
        labelProof
        (ay_vecp_conj_intro manifestAgreement checkerEvidence
          manifestProof checkerProof))

theorem ay_vecp_exit_contract_label
    (exitCode publicLabel manifestAgreement checkerEvidence : Prop) :
    AyVECPExitContract exitCode publicLabel manifestAgreement
      checkerEvidence ->
    publicLabel :=
  fun contract =>
    ay_vecp_conj_right exitCode
      (AyVECPConj publicLabel
        (AyVECPConj manifestAgreement checkerEvidence))
      contract publicLabel (fun labelProof _tail => labelProof)

theorem ay_vecp_exit_contract_manifest
    (exitCode publicLabel manifestAgreement checkerEvidence : Prop) :
    AyVECPExitContract exitCode publicLabel manifestAgreement
      checkerEvidence ->
    manifestAgreement :=
  fun contract =>
    ay_vecp_conj_right exitCode
      (AyVECPConj publicLabel
        (AyVECPConj manifestAgreement checkerEvidence))
      contract manifestAgreement
      (fun _labelProof tail =>
        tail manifestAgreement
          (fun manifestProof _checkerProof => manifestProof))

theorem ay_vecp_exit_contract_checker
    (exitCode publicLabel manifestAgreement checkerEvidence : Prop) :
    AyVECPExitContract exitCode publicLabel manifestAgreement
      checkerEvidence ->
    checkerEvidence :=
  fun contract =>
    ay_vecp_conj_right exitCode
      (AyVECPConj publicLabel
        (AyVECPConj manifestAgreement checkerEvidence))
      contract checkerEvidence
      (fun _labelProof tail =>
        tail checkerEvidence
          (fun _manifestProof checkerProof => checkerProof))

theorem ay_vecp_run_manifest_intro
    (runId formulaFingerprint preprocessChain artifactDigest : Prop) :
    runId -> formulaFingerprint -> preprocessChain -> artifactDigest ->
    AyVECPRunManifest runId formulaFingerprint preprocessChain
      artifactDigest :=
  fun runProof fingerprintProof preprocessProof digestProof =>
    ay_vecp_conj_intro runId
      (AyVECPConj formulaFingerprint
        (AyVECPConj preprocessChain artifactDigest))
      runProof
      (ay_vecp_conj_intro formulaFingerprint
        (AyVECPConj preprocessChain artifactDigest)
        fingerprintProof
        (ay_vecp_conj_intro preprocessChain artifactDigest preprocessProof
          digestProof))

theorem ay_vecp_model_evidence_intro
    (modelArtifact modelChecker manifestAgreement : Prop) :
    modelArtifact -> modelChecker -> manifestAgreement ->
    AyVECPModelEvidence modelArtifact modelChecker manifestAgreement :=
  fun artifactProof checkerProof manifestProof =>
    ay_vecp_conj_intro modelArtifact
      (AyVECPConj modelChecker manifestAgreement)
      artifactProof
      (ay_vecp_conj_intro modelChecker manifestAgreement checkerProof
        manifestProof)

theorem ay_vecp_model_evidence_checker
    (modelArtifact modelChecker manifestAgreement : Prop) :
    AyVECPModelEvidence modelArtifact modelChecker manifestAgreement ->
    modelChecker :=
  fun evidence =>
    ay_vecp_conj_right modelArtifact
      (AyVECPConj modelChecker manifestAgreement)
      evidence modelChecker (fun checkerProof _manifestProof =>
        checkerProof)

theorem ay_vecp_model_evidence_manifest
    (modelArtifact modelChecker manifestAgreement : Prop) :
    AyVECPModelEvidence modelArtifact modelChecker manifestAgreement ->
    manifestAgreement :=
  fun evidence =>
    ay_vecp_conj_right modelArtifact
      (AyVECPConj modelChecker manifestAgreement)
      evidence manifestAgreement (fun _checkerProof manifestProof =>
        manifestProof)

theorem ay_vecp_proof_evidence_intro
    (proofArtifact proofChecker manifestAgreement : Prop) :
    proofArtifact -> proofChecker -> manifestAgreement ->
    AyVECPProofEvidence proofArtifact proofChecker manifestAgreement :=
  fun artifactProof checkerProof manifestProof =>
    ay_vecp_conj_intro proofArtifact
      (AyVECPConj proofChecker manifestAgreement)
      artifactProof
      (ay_vecp_conj_intro proofChecker manifestAgreement checkerProof
        manifestProof)

theorem ay_vecp_proof_evidence_checker
    (proofArtifact proofChecker manifestAgreement : Prop) :
    AyVECPProofEvidence proofArtifact proofChecker manifestAgreement ->
    proofChecker :=
  fun evidence =>
    ay_vecp_conj_right proofArtifact
      (AyVECPConj proofChecker manifestAgreement)
      evidence proofChecker (fun checkerProof _manifestProof =>
        checkerProof)

theorem ay_vecp_proof_evidence_manifest
    (proofArtifact proofChecker manifestAgreement : Prop) :
    AyVECPProofEvidence proofArtifact proofChecker manifestAgreement ->
    manifestAgreement :=
  fun evidence =>
    ay_vecp_conj_right proofArtifact
      (AyVECPConj proofChecker manifestAgreement)
      evidence manifestAgreement (fun _checkerProof manifestProof =>
        manifestProof)

theorem ay_vecp_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVECPEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vecp_conj_intro exitCode
      (AyVECPConj artifacts
        (AyVECPConj checkerDecision (AyVECPConj auditDigest diagnostic)))
      exitProof
      (ay_vecp_conj_intro artifacts
        (AyVECPConj checkerDecision (AyVECPConj auditDigest diagnostic))
        artifactsProof
        (ay_vecp_conj_intro checkerDecision
          (AyVECPConj auditDigest diagnostic)
          checkerProof
          (ay_vecp_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vecp_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVECPEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vecp_conj_right exitCode
      (AyVECPConj artifacts
        (AyVECPConj checkerDecision (AyVECPConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vecp_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVECPMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vecp_conj_intro leafHash (AyVECPConj root entry)
      leafProof
      (ay_vecp_conj_intro root entry rootProof entryProof)

theorem ay_vecp_membership_entry (leafHash root entry : Prop) :
    AyVECPMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vecp_conj_right leafHash (AyVECPConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vecp_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVECPNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vecp_conj_intro reason (AyVECPConj auditDigest diagnostic)
      reasonProof
      (ay_vecp_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vecp_non_answer_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVECPNonAnswer reason auditDigest diagnostic :=
  ay_vecp_no_claim_intro reason auditDigest diagnostic

theorem ay_vecp_non_answer_no_claim
    (reason auditDigest diagnostic : Prop) :
    AyVECPNonAnswer reason auditDigest diagnostic ->
    AyVECPNoClaim reason auditDigest diagnostic :=
  fun nonAnswer => nonAnswer

theorem ay_vecp_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVECPRecomputeObligation reason auditDigest diagnostic :=
  ay_vecp_no_claim_intro reason auditDigest diagnostic

theorem ay_vecp_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVECPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVECPModel solver internalAssignment ->
    AyVECPVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vecp_model_intro original visibleAssignment
      (ay_vecp_equisat_backward original solver preprocess
        (ay_vecp_model_formula solver internalAssignment model))
      (decode (ay_vecp_model_assignment solver internalAssignment model))

theorem ay_vecp_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVECPPreprocessArtifact original solver ->
    AyVECPUnsat solver ->
    AyVECPUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vecp_equisat_forward original solver preprocess originalProof)

theorem ay_vecp_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVECPPreprocessArtifact original solver ->
    AyVECPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVECPUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vecp_equisat_forward original solver preprocess originalProof))

theorem ay_vecp_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVECPPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVECPModel solver internalAssignment) ->
    AyVECPMembership leafHash root
      (AyVECPEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVECPVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vecp_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vecp_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vecp_membership_entry leafHash root
            (AyVECPEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vecp_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVECPPreprocessArtifact original solver ->
    AyVECPReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVECPMembership leafHash root
      (AyVECPEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVECPUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vecp_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vecp_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vecp_membership_entry leafHash root
            (AyVECPEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vecp_sat_exit_public_sound
    (exitCode publicLabel manifestAgreement checkerEvidence
      satFact unsatFact noClaim : Prop) :
    AyVECPExitContract exitCode publicLabel manifestAgreement
      checkerEvidence ->
    (publicLabel -> manifestAgreement -> checkerEvidence -> satFact) ->
    AyVECPPublicResult satFact unsatFact noClaim :=
  fun contract sound =>
    fun result onSat _onTail =>
      onSat
        (sound
          (ay_vecp_exit_contract_label exitCode publicLabel
            manifestAgreement checkerEvidence contract)
          (ay_vecp_exit_contract_manifest exitCode publicLabel
            manifestAgreement checkerEvidence contract)
          (ay_vecp_exit_contract_checker exitCode publicLabel
            manifestAgreement checkerEvidence contract))

theorem ay_vecp_unsat_exit_public_sound
    (exitCode publicLabel manifestAgreement checkerEvidence
      satFact unsatFact noClaim : Prop) :
    AyVECPExitContract exitCode publicLabel manifestAgreement
      checkerEvidence ->
    (publicLabel -> manifestAgreement -> checkerEvidence -> unsatFact) ->
    AyVECPPublicResult satFact unsatFact noClaim :=
  fun contract sound =>
    ay_vecp_disj_right satFact (AyVECPDisj unsatFact noClaim)
      (fun result onUnsat _onNoClaim =>
        onUnsat
          (sound
            (ay_vecp_exit_contract_label exitCode publicLabel
              manifestAgreement checkerEvidence contract)
            (ay_vecp_exit_contract_manifest exitCode publicLabel
              manifestAgreement checkerEvidence contract)
            (ay_vecp_exit_contract_checker exitCode publicLabel
              manifestAgreement checkerEvidence contract)))

theorem ay_vecp_timeout_no_claim
    (timeout auditDigest diagnostic : Prop) :
    timeout -> auditDigest -> diagnostic ->
    AyVECPNoClaim timeout auditDigest diagnostic :=
  ay_vecp_no_claim_intro timeout auditDigest diagnostic

theorem ay_vecp_resource_exhaustion_no_claim
    (resourceExhaustion auditDigest diagnostic : Prop) :
    resourceExhaustion -> auditDigest -> diagnostic ->
    AyVECPNoClaim resourceExhaustion auditDigest diagnostic :=
  ay_vecp_no_claim_intro resourceExhaustion auditDigest diagnostic

theorem ay_vecp_replay_divergence_no_claim
    (replayDivergence auditDigest diagnostic : Prop) :
    replayDivergence -> auditDigest -> diagnostic ->
    AyVECPNoClaim replayDivergence auditDigest diagnostic :=
  ay_vecp_no_claim_intro replayDivergence auditDigest diagnostic

theorem ay_vecp_artifact_mismatch_no_claim
    (artifactMismatch auditDigest diagnostic : Prop) :
    artifactMismatch -> auditDigest -> diagnostic ->
    AyVECPNoClaim artifactMismatch auditDigest diagnostic :=
  ay_vecp_no_claim_intro artifactMismatch auditDigest diagnostic

theorem ay_vecp_non_answer_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVECPNonAnswer reason auditDigest diagnostic ->
    AyVECPPublicResult satFact unsatFact
      (AyVECPNoClaim reason auditDigest diagnostic) :=
  fun nonAnswer =>
    ay_vecp_disj_right satFact
      (AyVECPDisj unsatFact (AyVECPNoClaim reason auditDigest diagnostic))
      (ay_vecp_disj_right unsatFact
        (AyVECPNoClaim reason auditDigest diagnostic)
        (ay_vecp_non_answer_no_claim reason auditDigest diagnostic
          nonAnswer))

theorem ay_vecp_failure_recompute
    (timeout resourceExhaustion replayDivergence artifactMismatch
      auditDigest diagnostic recompute : Prop) :
    AyVECPDisj timeout
      (AyVECPDisj resourceExhaustion
        (AyVECPDisj replayDivergence artifactMismatch)) ->
    auditDigest -> diagnostic ->
    (timeout -> AyVECPRecomputeObligation timeout auditDigest diagnostic ->
      recompute) ->
    (resourceExhaustion ->
      AyVECPRecomputeObligation resourceExhaustion auditDigest diagnostic ->
      recompute) ->
    (replayDivergence ->
      AyVECPRecomputeObligation replayDivergence auditDigest diagnostic ->
      recompute) ->
    (artifactMismatch ->
      AyVECPRecomputeObligation artifactMismatch auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onTimeout onResource onReplay
      onArtifact =>
    failure recompute
      (fun timeoutProof =>
        onTimeout timeoutProof
          (ay_vecp_recompute_intro timeout auditDigest diagnostic
            timeoutProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun resourceProof =>
            onResource resourceProof
              (ay_vecp_recompute_intro resourceExhaustion auditDigest
                diagnostic resourceProof auditProof diagnosticProof))
          (fun tail2 =>
            tail2 recompute
              (fun replayProof =>
                onReplay replayProof
                  (ay_vecp_recompute_intro replayDivergence auditDigest
                    diagnostic replayProof auditProof diagnosticProof))
              (fun artifactProof =>
                onArtifact artifactProof
                  (ay_vecp_recompute_intro artifactMismatch auditDigest
                    diagnostic artifactProof auditProof diagnosticProof)))
