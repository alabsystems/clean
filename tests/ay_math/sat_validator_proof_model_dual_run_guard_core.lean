-- SAT-COMP proof/model dual-run guard soundness core.
--
-- Public SAT model artifacts and UNSAT proof artifacts may not be mixed across
-- separate or repeated runs.  Publication requires one run identity, matching
-- formula fingerprint, matching preprocessing chain, and the corresponding
-- proof-or-model checker evidence.  Mixed artifacts are no-claim recomputation
-- cases.

def AyVPMDConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVPMDDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVPMDEquisat (before after : Prop) : Prop :=
  AyVPMDConj (before -> after) (after -> before)

def AyVPMDPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVPMDDisj satFact (AyVPMDDisj unsatFact noClaim)

def AyVPMDRunGuard
    (runIdMatch fingerprintMatch preprocessMatch checkerEvidence : Prop) :
    Prop :=
  AyVPMDConj runIdMatch
    (AyVPMDConj fingerprintMatch
      (AyVPMDConj preprocessMatch checkerEvidence))

def AyVPMDSatArtifact
    (runId formulaFingerprint preprocessChain modelChecker : Prop) : Prop :=
  AyVPMDConj runId
    (AyVPMDConj formulaFingerprint
      (AyVPMDConj preprocessChain modelChecker))

def AyVPMDUnsatArtifact
    (runId formulaFingerprint preprocessChain proofChecker : Prop) : Prop :=
  AyVPMDConj runId
    (AyVPMDConj formulaFingerprint
      (AyVPMDConj preprocessChain proofChecker))

def AyVPMDPublicationBundle
    (selectedRun publicArtifact runGuard publicEvidence : Prop) : Prop :=
  AyVPMDConj selectedRun
    (AyVPMDConj publicArtifact
      (AyVPMDConj runGuard publicEvidence))

def AyVPMDEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVPMDConj exitCode
    (AyVPMDConj artifacts
      (AyVPMDConj checkerDecision
        (AyVPMDConj auditDigest diagnostic)))

def AyVPMDMembership (leafHash root entry : Prop) : Prop :=
  AyVPMDConj leafHash (AyVPMDConj root entry)

def AyVPMDNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVPMDConj reason (AyVPMDConj auditDigest diagnostic)

def AyVPMDRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVPMDConj reason (AyVPMDConj auditDigest diagnostic)

def AyVPMDModel (formula assignment : Prop) : Prop :=
  AyVPMDConj formula assignment

def AyVPMDUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVPMDVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVPMDModel original visibleAssignment

def AyVPMDPreprocessArtifact (original solver : Prop) : Prop :=
  AyVPMDEquisat original solver

def AyVPMDReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vpmd_conj_intro (left right : Prop) :
    left -> right -> AyVPMDConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vpmd_conj_left (left right : Prop) :
    AyVPMDConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vpmd_conj_right (left right : Prop) :
    AyVPMDConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vpmd_disj_right (left right : Prop) :
    right -> AyVPMDDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vpmd_equisat_forward (before after : Prop) :
    AyVPMDEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vpmd_equisat_backward (before after : Prop) :
    AyVPMDEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vpmd_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVPMDModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vpmd_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vpmd_model_formula (formula assignment : Prop) :
    AyVPMDModel formula assignment -> formula :=
  fun model => ay_vpmd_conj_left formula assignment model

theorem ay_vpmd_model_assignment (formula assignment : Prop) :
    AyVPMDModel formula assignment -> assignment :=
  fun model => ay_vpmd_conj_right formula assignment model

theorem ay_vpmd_run_guard_intro
    (runIdMatch fingerprintMatch preprocessMatch checkerEvidence : Prop) :
    runIdMatch -> fingerprintMatch -> preprocessMatch -> checkerEvidence ->
    AyVPMDRunGuard runIdMatch fingerprintMatch preprocessMatch
      checkerEvidence :=
  fun runProof fingerprintProof preprocessProof checkerProof =>
    ay_vpmd_conj_intro runIdMatch
      (AyVPMDConj fingerprintMatch
        (AyVPMDConj preprocessMatch checkerEvidence))
      runProof
      (ay_vpmd_conj_intro fingerprintMatch
        (AyVPMDConj preprocessMatch checkerEvidence)
        fingerprintProof
        (ay_vpmd_conj_intro preprocessMatch checkerEvidence
          preprocessProof checkerProof))

theorem ay_vpmd_run_guard_run_id
    (runIdMatch fingerprintMatch preprocessMatch checkerEvidence : Prop) :
    AyVPMDRunGuard runIdMatch fingerprintMatch preprocessMatch
      checkerEvidence ->
    runIdMatch :=
  fun guard =>
    ay_vpmd_conj_left runIdMatch
      (AyVPMDConj fingerprintMatch
        (AyVPMDConj preprocessMatch checkerEvidence))
      guard

theorem ay_vpmd_run_guard_fingerprint
    (runIdMatch fingerprintMatch preprocessMatch checkerEvidence : Prop) :
    AyVPMDRunGuard runIdMatch fingerprintMatch preprocessMatch
      checkerEvidence ->
    fingerprintMatch :=
  fun guard =>
    ay_vpmd_conj_right runIdMatch
      (AyVPMDConj fingerprintMatch
        (AyVPMDConj preprocessMatch checkerEvidence))
      guard fingerprintMatch
      (fun fingerprintProof _tail => fingerprintProof)

theorem ay_vpmd_run_guard_preprocess
    (runIdMatch fingerprintMatch preprocessMatch checkerEvidence : Prop) :
    AyVPMDRunGuard runIdMatch fingerprintMatch preprocessMatch
      checkerEvidence ->
    preprocessMatch :=
  fun guard =>
    ay_vpmd_conj_right runIdMatch
      (AyVPMDConj fingerprintMatch
        (AyVPMDConj preprocessMatch checkerEvidence))
      guard preprocessMatch
      (fun _fingerprintProof tail =>
        tail preprocessMatch
          (fun preprocessProof _checkerProof => preprocessProof))

theorem ay_vpmd_run_guard_checker
    (runIdMatch fingerprintMatch preprocessMatch checkerEvidence : Prop) :
    AyVPMDRunGuard runIdMatch fingerprintMatch preprocessMatch
      checkerEvidence ->
    checkerEvidence :=
  fun guard =>
    ay_vpmd_conj_right runIdMatch
      (AyVPMDConj fingerprintMatch
        (AyVPMDConj preprocessMatch checkerEvidence))
      guard checkerEvidence
      (fun _fingerprintProof tail =>
        tail checkerEvidence
          (fun _preprocessProof checkerProof => checkerProof))

theorem ay_vpmd_sat_artifact_intro
    (runId formulaFingerprint preprocessChain modelChecker : Prop) :
    runId -> formulaFingerprint -> preprocessChain -> modelChecker ->
    AyVPMDSatArtifact runId formulaFingerprint preprocessChain modelChecker :=
  fun runProof fingerprintProof preprocessProof checkerProof =>
    ay_vpmd_conj_intro runId
      (AyVPMDConj formulaFingerprint
        (AyVPMDConj preprocessChain modelChecker))
      runProof
      (ay_vpmd_conj_intro formulaFingerprint
        (AyVPMDConj preprocessChain modelChecker)
        fingerprintProof
        (ay_vpmd_conj_intro preprocessChain modelChecker preprocessProof
          checkerProof))

theorem ay_vpmd_unsat_artifact_intro
    (runId formulaFingerprint preprocessChain proofChecker : Prop) :
    runId -> formulaFingerprint -> preprocessChain -> proofChecker ->
    AyVPMDUnsatArtifact runId formulaFingerprint preprocessChain
      proofChecker :=
  fun runProof fingerprintProof preprocessProof checkerProof =>
    ay_vpmd_conj_intro runId
      (AyVPMDConj formulaFingerprint
        (AyVPMDConj preprocessChain proofChecker))
      runProof
      (ay_vpmd_conj_intro formulaFingerprint
        (AyVPMDConj preprocessChain proofChecker)
        fingerprintProof
        (ay_vpmd_conj_intro preprocessChain proofChecker preprocessProof
          checkerProof))

theorem ay_vpmd_publication_bundle_intro
    (selectedRun publicArtifact runGuard publicEvidence : Prop) :
    selectedRun -> publicArtifact -> runGuard -> publicEvidence ->
    AyVPMDPublicationBundle selectedRun publicArtifact runGuard
      publicEvidence :=
  fun runProof artifactProof guardProof evidenceProof =>
    ay_vpmd_conj_intro selectedRun
      (AyVPMDConj publicArtifact
        (AyVPMDConj runGuard publicEvidence))
      runProof
      (ay_vpmd_conj_intro publicArtifact
        (AyVPMDConj runGuard publicEvidence)
        artifactProof
        (ay_vpmd_conj_intro runGuard publicEvidence guardProof
          evidenceProof))

theorem ay_vpmd_publication_bundle_run
    (selectedRun publicArtifact runGuard publicEvidence : Prop) :
    AyVPMDPublicationBundle selectedRun publicArtifact runGuard
      publicEvidence ->
    selectedRun :=
  fun bundle =>
    ay_vpmd_conj_left selectedRun
      (AyVPMDConj publicArtifact
        (AyVPMDConj runGuard publicEvidence))
      bundle

theorem ay_vpmd_publication_bundle_guard
    (selectedRun publicArtifact runGuard publicEvidence : Prop) :
    AyVPMDPublicationBundle selectedRun publicArtifact runGuard
      publicEvidence ->
    runGuard :=
  fun bundle =>
    ay_vpmd_conj_right selectedRun
      (AyVPMDConj publicArtifact
        (AyVPMDConj runGuard publicEvidence))
      bundle runGuard
      (fun _artifactProof tail =>
        tail runGuard (fun guardProof _evidenceProof => guardProof))

theorem ay_vpmd_publication_bundle_evidence
    (selectedRun publicArtifact runGuard publicEvidence : Prop) :
    AyVPMDPublicationBundle selectedRun publicArtifact runGuard
      publicEvidence ->
    publicEvidence :=
  fun bundle =>
    ay_vpmd_conj_right selectedRun
      (AyVPMDConj publicArtifact
        (AyVPMDConj runGuard publicEvidence))
      bundle publicEvidence
      (fun _artifactProof tail =>
        tail publicEvidence (fun _guardProof evidenceProof =>
          evidenceProof))

theorem ay_vpmd_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVPMDEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vpmd_conj_intro exitCode
      (AyVPMDConj artifacts
        (AyVPMDConj checkerDecision (AyVPMDConj auditDigest diagnostic)))
      exitProof
      (ay_vpmd_conj_intro artifacts
        (AyVPMDConj checkerDecision (AyVPMDConj auditDigest diagnostic))
        artifactsProof
        (ay_vpmd_conj_intro checkerDecision
          (AyVPMDConj auditDigest diagnostic)
          checkerProof
          (ay_vpmd_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vpmd_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVPMDEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vpmd_conj_right exitCode
      (AyVPMDConj artifacts
        (AyVPMDConj checkerDecision (AyVPMDConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vpmd_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVPMDMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vpmd_conj_intro leafHash (AyVPMDConj root entry)
      leafProof
      (ay_vpmd_conj_intro root entry rootProof entryProof)

theorem ay_vpmd_membership_entry (leafHash root entry : Prop) :
    AyVPMDMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vpmd_conj_right leafHash (AyVPMDConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vpmd_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVPMDNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vpmd_conj_intro reason (AyVPMDConj auditDigest diagnostic)
      reasonProof
      (ay_vpmd_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vpmd_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVPMDRecomputeObligation reason auditDigest diagnostic :=
  ay_vpmd_no_claim_intro reason auditDigest diagnostic

theorem ay_vpmd_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVPMDPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVPMDModel solver internalAssignment ->
    AyVPMDVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vpmd_model_intro original visibleAssignment
      (ay_vpmd_equisat_backward original solver preprocess
        (ay_vpmd_model_formula solver internalAssignment model))
      (decode (ay_vpmd_model_assignment solver internalAssignment model))

theorem ay_vpmd_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVPMDPreprocessArtifact original solver ->
    AyVPMDUnsat solver ->
    AyVPMDUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vpmd_equisat_forward original solver preprocess originalProof)

theorem ay_vpmd_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVPMDPreprocessArtifact original solver ->
    AyVPMDReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVPMDUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vpmd_equisat_forward original solver preprocess originalProof))

theorem ay_vpmd_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVPMDPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVPMDModel solver internalAssignment) ->
    AyVPMDMembership leafHash root
      (AyVPMDEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVPMDVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vpmd_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vpmd_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vpmd_membership_entry leafHash root
            (AyVPMDEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vpmd_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVPMDPreprocessArtifact original solver ->
    AyVPMDReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVPMDMembership leafHash root
      (AyVPMDEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVPMDUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vpmd_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vpmd_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vpmd_membership_entry leafHash root
            (AyVPMDEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vpmd_single_run_public_sound
    (selectedRun publicArtifact runGuard publicEvidence
      satFact unsatFact noClaim : Prop) :
    AyVPMDPublicationBundle selectedRun publicArtifact runGuard
      publicEvidence ->
    (selectedRun -> runGuard -> publicEvidence ->
      AyVPMDPublicResult satFact unsatFact noClaim) ->
    AyVPMDPublicResult satFact unsatFact noClaim :=
  fun bundle sound =>
    sound
      (ay_vpmd_publication_bundle_run selectedRun publicArtifact runGuard
        publicEvidence bundle)
      (ay_vpmd_publication_bundle_guard selectedRun publicArtifact runGuard
        publicEvidence bundle)
      (ay_vpmd_publication_bundle_evidence selectedRun publicArtifact
        runGuard publicEvidence bundle)

theorem ay_vpmd_single_run_preserves_sat
    (selectedRun publicArtifact runGuard publicEvidence satFact : Prop) :
    AyVPMDPublicationBundle selectedRun publicArtifact runGuard
      publicEvidence ->
    (runGuard -> publicEvidence -> satFact) ->
    satFact :=
  fun bundle sound =>
    sound
      (ay_vpmd_publication_bundle_guard selectedRun publicArtifact runGuard
        publicEvidence bundle)
      (ay_vpmd_publication_bundle_evidence selectedRun publicArtifact
        runGuard publicEvidence bundle)

theorem ay_vpmd_single_run_preserves_unsat
    (selectedRun publicArtifact runGuard publicEvidence unsatFact : Prop) :
    AyVPMDPublicationBundle selectedRun publicArtifact runGuard
      publicEvidence ->
    (runGuard -> publicEvidence -> unsatFact) ->
    unsatFact :=
  fun bundle sound =>
    sound
      (ay_vpmd_publication_bundle_guard selectedRun publicArtifact runGuard
        publicEvidence bundle)
      (ay_vpmd_publication_bundle_evidence selectedRun publicArtifact
        runGuard publicEvidence bundle)

theorem ay_vpmd_mixed_artifacts_no_claim
    (mixedArtifacts auditDigest diagnostic : Prop) :
    mixedArtifacts -> auditDigest -> diagnostic ->
    AyVPMDNoClaim mixedArtifacts auditDigest diagnostic :=
  ay_vpmd_no_claim_intro mixedArtifacts auditDigest diagnostic

theorem ay_vpmd_wrong_run_no_claim
    (wrongRun auditDigest diagnostic : Prop) :
    wrongRun -> auditDigest -> diagnostic ->
    AyVPMDNoClaim wrongRun auditDigest diagnostic :=
  ay_vpmd_no_claim_intro wrongRun auditDigest diagnostic

theorem ay_vpmd_fingerprint_mismatch_no_claim
    (fingerprintMismatch auditDigest diagnostic : Prop) :
    fingerprintMismatch -> auditDigest -> diagnostic ->
    AyVPMDNoClaim fingerprintMismatch auditDigest diagnostic :=
  ay_vpmd_no_claim_intro fingerprintMismatch auditDigest diagnostic

theorem ay_vpmd_preprocess_mismatch_no_claim
    (preprocessMismatch auditDigest diagnostic : Prop) :
    preprocessMismatch -> auditDigest -> diagnostic ->
    AyVPMDNoClaim preprocessMismatch auditDigest diagnostic :=
  ay_vpmd_no_claim_intro preprocessMismatch auditDigest diagnostic

theorem ay_vpmd_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVPMDNoClaim reason auditDigest diagnostic ->
    AyVPMDPublicResult satFact unsatFact
      (AyVPMDNoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vpmd_disj_right satFact
      (AyVPMDDisj unsatFact
        (AyVPMDNoClaim reason auditDigest diagnostic))
      (ay_vpmd_disj_right unsatFact
        (AyVPMDNoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vpmd_mixed_or_mismatched_recompute
    (mixedArtifacts wrongRun fingerprintMismatch preprocessMismatch
      auditDigest diagnostic recompute : Prop) :
    AyVPMDDisj mixedArtifacts
      (AyVPMDDisj wrongRun
        (AyVPMDDisj fingerprintMismatch preprocessMismatch)) ->
    auditDigest -> diagnostic ->
    (mixedArtifacts ->
      AyVPMDRecomputeObligation mixedArtifacts auditDigest diagnostic ->
      recompute) ->
    (wrongRun ->
      AyVPMDRecomputeObligation wrongRun auditDigest diagnostic ->
      recompute) ->
    (fingerprintMismatch ->
      AyVPMDRecomputeObligation fingerprintMismatch auditDigest diagnostic ->
      recompute) ->
    (preprocessMismatch ->
      AyVPMDRecomputeObligation preprocessMismatch auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onMixed onRun onFingerprint
      onPreprocess =>
    failure recompute
      (fun mixedProof =>
        onMixed mixedProof
          (ay_vpmd_recompute_intro mixedArtifacts auditDigest diagnostic
            mixedProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun runProof =>
            onRun runProof
              (ay_vpmd_recompute_intro wrongRun auditDigest diagnostic
                runProof auditProof diagnosticProof))
          (fun tail2 =>
            tail2 recompute
              (fun fingerprintProof =>
                onFingerprint fingerprintProof
                  (ay_vpmd_recompute_intro fingerprintMismatch auditDigest
                    diagnostic fingerprintProof auditProof diagnosticProof))
              (fun preprocessProof =>
                onPreprocess preprocessProof
                  (ay_vpmd_recompute_intro preprocessMismatch auditDigest
                    diagnostic preprocessProof auditProof diagnosticProof)))
