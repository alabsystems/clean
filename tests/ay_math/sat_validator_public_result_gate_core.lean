-- SAT-COMP validator public result gate core.
--
-- ay may emit a public SAT/UNSAT answer only when formula fingerprint,
-- exit-code contract, checker replay, preprocessing reconstruction,
-- append-only manifest membership, and absence of diagnostics all agree.
-- Missing or stale evidence routes to no-claim/recompute.

def AyVPRGConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVPRGDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVPRGEquisat (before after : Prop) : Prop :=
  AyVPRGConj (before -> after) (after -> before)

def AyVPRGPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVPRGDisj satFact (AyVPRGDisj unsatFact noClaim)

def AyVPRGGateEvidence
    (formulaFingerprint exitContract checkerReplay preprocessReconstruction
      manifestMembership noDiagnostics : Prop) : Prop :=
  AyVPRGConj formulaFingerprint
    (AyVPRGConj exitContract
      (AyVPRGConj checkerReplay
        (AyVPRGConj preprocessReconstruction
          (AyVPRGConj manifestMembership noDiagnostics))))

def AyVPRGSatGate (gateEvidence modelArtifact originalModel : Prop) : Prop :=
  AyVPRGConj gateEvidence (AyVPRGConj modelArtifact originalModel)

def AyVPRGUnsatGate
    (gateEvidence proofArtifact originalEmptyClause : Prop) : Prop :=
  AyVPRGConj gateEvidence
    (AyVPRGConj proofArtifact originalEmptyClause)

def AyVPRGEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVPRGConj exitCode
    (AyVPRGConj artifacts
      (AyVPRGConj checkerDecision
        (AyVPRGConj auditDigest diagnostic)))

def AyVPRGMembership (leafHash root entry : Prop) : Prop :=
  AyVPRGConj leafHash (AyVPRGConj root entry)

def AyVPRGNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVPRGConj reason (AyVPRGConj auditDigest diagnostic)

def AyVPRGRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVPRGConj reason (AyVPRGConj auditDigest diagnostic)

def AyVPRGModel (formula assignment : Prop) : Prop :=
  AyVPRGConj formula assignment

def AyVPRGUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVPRGVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVPRGModel original visibleAssignment

def AyVPRGPreprocessArtifact (original solver : Prop) : Prop :=
  AyVPRGEquisat original solver

def AyVPRGReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vprg_conj_intro (left right : Prop) :
    left -> right -> AyVPRGConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vprg_conj_left (left right : Prop) :
    AyVPRGConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vprg_conj_right (left right : Prop) :
    AyVPRGConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vprg_disj_right (left right : Prop) :
    right -> AyVPRGDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vprg_equisat_forward (before after : Prop) :
    AyVPRGEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vprg_equisat_backward (before after : Prop) :
    AyVPRGEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vprg_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVPRGModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vprg_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vprg_model_formula (formula assignment : Prop) :
    AyVPRGModel formula assignment -> formula :=
  fun model => ay_vprg_conj_left formula assignment model

theorem ay_vprg_model_assignment (formula assignment : Prop) :
    AyVPRGModel formula assignment -> assignment :=
  fun model => ay_vprg_conj_right formula assignment model

theorem ay_vprg_gate_evidence_intro
    (formulaFingerprint exitContract checkerReplay preprocessReconstruction
      manifestMembership noDiagnostics : Prop) :
    formulaFingerprint -> exitContract -> checkerReplay ->
    preprocessReconstruction -> manifestMembership -> noDiagnostics ->
    AyVPRGGateEvidence formulaFingerprint exitContract checkerReplay
      preprocessReconstruction manifestMembership noDiagnostics :=
  fun fingerprintProof exitProof replayProof reconstructProof membershipProof
      cleanProof =>
    ay_vprg_conj_intro formulaFingerprint
      (AyVPRGConj exitContract
        (AyVPRGConj checkerReplay
          (AyVPRGConj preprocessReconstruction
            (AyVPRGConj manifestMembership noDiagnostics))))
      fingerprintProof
      (ay_vprg_conj_intro exitContract
        (AyVPRGConj checkerReplay
          (AyVPRGConj preprocessReconstruction
            (AyVPRGConj manifestMembership noDiagnostics)))
        exitProof
        (ay_vprg_conj_intro checkerReplay
          (AyVPRGConj preprocessReconstruction
            (AyVPRGConj manifestMembership noDiagnostics))
          replayProof
          (ay_vprg_conj_intro preprocessReconstruction
            (AyVPRGConj manifestMembership noDiagnostics)
            reconstructProof
            (ay_vprg_conj_intro manifestMembership noDiagnostics
              membershipProof cleanProof))))

theorem ay_vprg_gate_evidence_replay
    (formulaFingerprint exitContract checkerReplay preprocessReconstruction
      manifestMembership noDiagnostics : Prop) :
    AyVPRGGateEvidence formulaFingerprint exitContract checkerReplay
      preprocessReconstruction manifestMembership noDiagnostics ->
    checkerReplay :=
  fun evidence =>
    ay_vprg_conj_right formulaFingerprint
      (AyVPRGConj exitContract
        (AyVPRGConj checkerReplay
          (AyVPRGConj preprocessReconstruction
            (AyVPRGConj manifestMembership noDiagnostics))))
      evidence checkerReplay
      (fun _exitProof tail =>
        tail checkerReplay (fun replayProof _tail2 => replayProof))

theorem ay_vprg_gate_evidence_reconstruction
    (formulaFingerprint exitContract checkerReplay preprocessReconstruction
      manifestMembership noDiagnostics : Prop) :
    AyVPRGGateEvidence formulaFingerprint exitContract checkerReplay
      preprocessReconstruction manifestMembership noDiagnostics ->
    preprocessReconstruction :=
  fun evidence =>
    ay_vprg_conj_right formulaFingerprint
      (AyVPRGConj exitContract
        (AyVPRGConj checkerReplay
          (AyVPRGConj preprocessReconstruction
            (AyVPRGConj manifestMembership noDiagnostics))))
      evidence preprocessReconstruction
      (fun _exitProof tail =>
        tail preprocessReconstruction
          (fun _replayProof tail2 =>
            tail2 preprocessReconstruction
              (fun reconstructionProof _tail3 => reconstructionProof)))

theorem ay_vprg_gate_evidence_manifest
    (formulaFingerprint exitContract checkerReplay preprocessReconstruction
      manifestMembership noDiagnostics : Prop) :
    AyVPRGGateEvidence formulaFingerprint exitContract checkerReplay
      preprocessReconstruction manifestMembership noDiagnostics ->
    manifestMembership :=
  fun evidence =>
    ay_vprg_conj_right formulaFingerprint
      (AyVPRGConj exitContract
        (AyVPRGConj checkerReplay
          (AyVPRGConj preprocessReconstruction
            (AyVPRGConj manifestMembership noDiagnostics))))
      evidence manifestMembership
      (fun _exitProof tail =>
        tail manifestMembership
          (fun _replayProof tail2 =>
            tail2 manifestMembership
              (fun _reconstructionProof tail3 =>
                tail3 manifestMembership
                  (fun membershipProof _cleanProof => membershipProof))))

theorem ay_vprg_sat_gate_intro
    (gateEvidence modelArtifact originalModel : Prop) :
    gateEvidence -> modelArtifact -> originalModel ->
    AyVPRGSatGate gateEvidence modelArtifact originalModel :=
  fun evidenceProof artifactProof modelProof =>
    ay_vprg_conj_intro gateEvidence
      (AyVPRGConj modelArtifact originalModel)
      evidenceProof
      (ay_vprg_conj_intro modelArtifact originalModel artifactProof
        modelProof)

theorem ay_vprg_sat_gate_evidence
    (gateEvidence modelArtifact originalModel : Prop) :
    AyVPRGSatGate gateEvidence modelArtifact originalModel ->
    gateEvidence :=
  fun gate =>
    ay_vprg_conj_left gateEvidence
      (AyVPRGConj modelArtifact originalModel) gate

theorem ay_vprg_sat_gate_model
    (gateEvidence modelArtifact originalModel : Prop) :
    AyVPRGSatGate gateEvidence modelArtifact originalModel ->
    originalModel :=
  fun gate =>
    ay_vprg_conj_right gateEvidence
      (AyVPRGConj modelArtifact originalModel)
      gate originalModel (fun _artifactProof modelProof => modelProof)

theorem ay_vprg_unsat_gate_intro
    (gateEvidence proofArtifact originalEmptyClause : Prop) :
    gateEvidence -> proofArtifact -> originalEmptyClause ->
    AyVPRGUnsatGate gateEvidence proofArtifact originalEmptyClause :=
  fun evidenceProof artifactProof proofProof =>
    ay_vprg_conj_intro gateEvidence
      (AyVPRGConj proofArtifact originalEmptyClause)
      evidenceProof
      (ay_vprg_conj_intro proofArtifact originalEmptyClause artifactProof
        proofProof)

theorem ay_vprg_unsat_gate_evidence
    (gateEvidence proofArtifact originalEmptyClause : Prop) :
    AyVPRGUnsatGate gateEvidence proofArtifact originalEmptyClause ->
    gateEvidence :=
  fun gate =>
    ay_vprg_conj_left gateEvidence
      (AyVPRGConj proofArtifact originalEmptyClause) gate

theorem ay_vprg_unsat_gate_empty_clause
    (gateEvidence proofArtifact originalEmptyClause : Prop) :
    AyVPRGUnsatGate gateEvidence proofArtifact originalEmptyClause ->
    originalEmptyClause :=
  fun gate =>
    ay_vprg_conj_right gateEvidence
      (AyVPRGConj proofArtifact originalEmptyClause)
      gate originalEmptyClause
      (fun _artifactProof proofProof => proofProof)

theorem ay_vprg_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVPRGEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vprg_conj_intro exitCode
      (AyVPRGConj artifacts
        (AyVPRGConj checkerDecision (AyVPRGConj auditDigest diagnostic)))
      exitProof
      (ay_vprg_conj_intro artifacts
        (AyVPRGConj checkerDecision (AyVPRGConj auditDigest diagnostic))
        artifactsProof
        (ay_vprg_conj_intro checkerDecision
          (AyVPRGConj auditDigest diagnostic)
          checkerProof
          (ay_vprg_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vprg_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVPRGEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vprg_conj_right exitCode
      (AyVPRGConj artifacts
        (AyVPRGConj checkerDecision (AyVPRGConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vprg_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVPRGMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vprg_conj_intro leafHash (AyVPRGConj root entry)
      leafProof
      (ay_vprg_conj_intro root entry rootProof entryProof)

theorem ay_vprg_membership_entry (leafHash root entry : Prop) :
    AyVPRGMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vprg_conj_right leafHash (AyVPRGConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vprg_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVPRGNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vprg_conj_intro reason (AyVPRGConj auditDigest diagnostic)
      reasonProof
      (ay_vprg_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vprg_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVPRGRecomputeObligation reason auditDigest diagnostic :=
  ay_vprg_no_claim_intro reason auditDigest diagnostic

theorem ay_vprg_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVPRGPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVPRGModel solver internalAssignment ->
    AyVPRGVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vprg_model_intro original visibleAssignment
      (ay_vprg_equisat_backward original solver preprocess
        (ay_vprg_model_formula solver internalAssignment model))
      (decode (ay_vprg_model_assignment solver internalAssignment model))

theorem ay_vprg_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVPRGPreprocessArtifact original solver ->
    AyVPRGUnsat solver ->
    AyVPRGUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vprg_equisat_forward original solver preprocess originalProof)

theorem ay_vprg_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVPRGPreprocessArtifact original solver ->
    AyVPRGReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVPRGUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vprg_equisat_forward original solver preprocess originalProof))

theorem ay_vprg_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVPRGPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVPRGModel solver internalAssignment) ->
    AyVPRGMembership leafHash root
      (AyVPRGEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVPRGVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vprg_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vprg_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vprg_membership_entry leafHash root
            (AyVPRGEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vprg_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVPRGPreprocessArtifact original solver ->
    AyVPRGReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVPRGMembership leafHash root
      (AyVPRGEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVPRGUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vprg_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vprg_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vprg_membership_entry leafHash root
            (AyVPRGEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vprg_accepted_sat_gate_original_model
    (gateEvidence modelArtifact originalModel : Prop) :
    AyVPRGSatGate gateEvidence modelArtifact originalModel ->
    originalModel :=
  ay_vprg_sat_gate_model gateEvidence modelArtifact originalModel

theorem ay_vprg_accepted_unsat_gate_original_empty_clause
    (gateEvidence proofArtifact originalEmptyClause : Prop) :
    AyVPRGUnsatGate gateEvidence proofArtifact originalEmptyClause ->
    originalEmptyClause :=
  ay_vprg_unsat_gate_empty_clause gateEvidence proofArtifact
    originalEmptyClause

theorem ay_vprg_sat_gate_public_sound
    (gateEvidence modelArtifact originalModel satFact unsatFact noClaim :
      Prop) :
    AyVPRGSatGate gateEvidence modelArtifact originalModel ->
    (gateEvidence -> originalModel -> satFact) ->
    AyVPRGPublicResult satFact unsatFact noClaim :=
  fun gate sound result onSat _onTail =>
    onSat
      (sound
        (ay_vprg_sat_gate_evidence gateEvidence modelArtifact
          originalModel gate)
        (ay_vprg_sat_gate_model gateEvidence modelArtifact originalModel
          gate))

theorem ay_vprg_unsat_gate_public_sound
    (gateEvidence proofArtifact originalEmptyClause satFact unsatFact
      noClaim : Prop) :
    AyVPRGUnsatGate gateEvidence proofArtifact originalEmptyClause ->
    (gateEvidence -> originalEmptyClause -> unsatFact) ->
    AyVPRGPublicResult satFact unsatFact noClaim :=
  fun gate sound =>
    ay_vprg_disj_right satFact (AyVPRGDisj unsatFact noClaim)
      (fun result onUnsat _onNoClaim =>
        onUnsat
          (sound
            (ay_vprg_unsat_gate_evidence gateEvidence proofArtifact
              originalEmptyClause gate)
            (ay_vprg_unsat_gate_empty_clause gateEvidence proofArtifact
              originalEmptyClause gate)))

theorem ay_vprg_missing_checker_no_claim
    (missingChecker auditDigest diagnostic : Prop) :
    missingChecker -> auditDigest -> diagnostic ->
    AyVPRGNoClaim missingChecker auditDigest diagnostic :=
  ay_vprg_no_claim_intro missingChecker auditDigest diagnostic

theorem ay_vprg_stale_digest_no_claim
    (staleDigest auditDigest diagnostic : Prop) :
    staleDigest -> auditDigest -> diagnostic ->
    AyVPRGNoClaim staleDigest auditDigest diagnostic :=
  ay_vprg_no_claim_intro staleDigest auditDigest diagnostic

theorem ay_vprg_reconstruction_mismatch_no_claim
    (reconstructionMismatch auditDigest diagnostic : Prop) :
    reconstructionMismatch -> auditDigest -> diagnostic ->
    AyVPRGNoClaim reconstructionMismatch auditDigest diagnostic :=
  ay_vprg_no_claim_intro reconstructionMismatch auditDigest diagnostic

theorem ay_vprg_diagnostic_no_claim
    (diagnosticNoClaim auditDigest diagnostic : Prop) :
    diagnosticNoClaim -> auditDigest -> diagnostic ->
    AyVPRGNoClaim diagnosticNoClaim auditDigest diagnostic :=
  ay_vprg_no_claim_intro diagnosticNoClaim auditDigest diagnostic

theorem ay_vprg_exit_code_mismatch_no_claim
    (exitCodeMismatch auditDigest diagnostic : Prop) :
    exitCodeMismatch -> auditDigest -> diagnostic ->
    AyVPRGNoClaim exitCodeMismatch auditDigest diagnostic :=
  ay_vprg_no_claim_intro exitCodeMismatch auditDigest diagnostic

theorem ay_vprg_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVPRGNoClaim reason auditDigest diagnostic ->
    AyVPRGPublicResult satFact unsatFact
      (AyVPRGNoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vprg_disj_right satFact
      (AyVPRGDisj unsatFact
        (AyVPRGNoClaim reason auditDigest diagnostic))
      (ay_vprg_disj_right unsatFact
        (AyVPRGNoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vprg_gate_failure_recompute
    (missingChecker staleDigest reconstructionMismatch diagnosticNoClaim
      exitCodeMismatch auditDigest diagnostic recompute : Prop) :
    AyVPRGDisj missingChecker
      (AyVPRGDisj staleDigest
        (AyVPRGDisj reconstructionMismatch
          (AyVPRGDisj diagnosticNoClaim exitCodeMismatch))) ->
    auditDigest -> diagnostic ->
    (missingChecker ->
      AyVPRGRecomputeObligation missingChecker auditDigest diagnostic ->
      recompute) ->
    (staleDigest ->
      AyVPRGRecomputeObligation staleDigest auditDigest diagnostic ->
      recompute) ->
    (reconstructionMismatch ->
      AyVPRGRecomputeObligation reconstructionMismatch auditDigest diagnostic ->
      recompute) ->
    (diagnosticNoClaim ->
      AyVPRGRecomputeObligation diagnosticNoClaim auditDigest diagnostic ->
      recompute) ->
    (exitCodeMismatch ->
      AyVPRGRecomputeObligation exitCodeMismatch auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onMissing onStale onReconstruct
      onDiagnostic onExit =>
    failure recompute
      (fun missingProof =>
        onMissing missingProof
          (ay_vprg_recompute_intro missingChecker auditDigest diagnostic
            missingProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun staleProof =>
            onStale staleProof
              (ay_vprg_recompute_intro staleDigest auditDigest diagnostic
                staleProof auditProof diagnosticProof))
          (fun tail2 =>
            tail2 recompute
              (fun reconstructProof =>
                onReconstruct reconstructProof
                  (ay_vprg_recompute_intro reconstructionMismatch auditDigest
                    diagnostic reconstructProof auditProof diagnosticProof))
              (fun tail3 =>
                tail3 recompute
                  (fun diagnosticProof2 =>
                    onDiagnostic diagnosticProof2
                      (ay_vprg_recompute_intro diagnosticNoClaim auditDigest
                        diagnostic diagnosticProof2 auditProof
                        diagnosticProof))
                  (fun exitProof =>
                    onExit exitProof
                      (ay_vprg_recompute_intro exitCodeMismatch auditDigest
                        diagnostic exitProof auditProof diagnosticProof))))
