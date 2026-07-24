-- SAT-COMP sequential-main portfolio manifest soundness core.
--
-- Sequential Main may select one solver configuration before a run only when
-- the manifest, benchmark evidence, checker replay, formula fingerprint, and
-- public SAT/UNSAT evidence agree.  Stale profiles and wrong manifests are
-- fallback/no-claim cases, not publishable competition results.

def AyVSPMConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVSPMDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVSPMEquisat (before after : Prop) : Prop :=
  AyVSPMConj (before -> after) (after -> before)

def AyVSPMPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVSPMDisj satFact (AyVSPMDisj unsatFact noClaim)

def AyVSPMPolicyManifest
    (manifestId selectedPolicy preprocessingProfile fingerprint : Prop) :
    Prop :=
  AyVSPMConj manifestId
    (AyVSPMConj selectedPolicy
      (AyVSPMConj preprocessingProfile fingerprint))

def AyVSPMRunEvidence
    (benchmarkEvidence checkerReplay formulaFingerprint publicEvidence :
      Prop) : Prop :=
  AyVSPMConj benchmarkEvidence
    (AyVSPMConj checkerReplay
      (AyVSPMConj formulaFingerprint publicEvidence))

def AyVSPMManifestAgreement
    (manifestMatch benchmarkMatch replayMatch fingerprintMatch
      publicMatch : Prop) : Prop :=
  AyVSPMConj manifestMatch
    (AyVSPMConj benchmarkMatch
      (AyVSPMConj replayMatch
        (AyVSPMConj fingerprintMatch publicMatch)))

def AyVSPMSequentialSelection
    (policyManifest runEvidence manifestAgreement selectedRun : Prop) :
    Prop :=
  AyVSPMConj policyManifest
    (AyVSPMConj runEvidence
      (AyVSPMConj manifestAgreement selectedRun))

def AyVSPMEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVSPMConj exitCode
    (AyVSPMConj artifacts
      (AyVSPMConj checkerDecision
        (AyVSPMConj auditDigest diagnostic)))

def AyVSPMMembership (leafHash root entry : Prop) : Prop :=
  AyVSPMConj leafHash (AyVSPMConj root entry)

def AyVSPMFallback (reason auditDigest diagnostic : Prop) : Prop :=
  AyVSPMConj reason (AyVSPMConj auditDigest diagnostic)

def AyVSPMNoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVSPMConj reason (AyVSPMConj auditDigest diagnostic)

def AyVSPMModel (formula assignment : Prop) : Prop :=
  AyVSPMConj formula assignment

def AyVSPMUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVSPMVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVSPMModel original visibleAssignment

def AyVSPMPreprocessArtifact (original solver : Prop) : Prop :=
  AyVSPMEquisat original solver

def AyVSPMReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vspm_conj_intro (left right : Prop) :
    left -> right -> AyVSPMConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vspm_conj_left (left right : Prop) :
    AyVSPMConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vspm_conj_right (left right : Prop) :
    AyVSPMConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vspm_disj_right (left right : Prop) :
    right -> AyVSPMDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vspm_equisat_forward (before after : Prop) :
    AyVSPMEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vspm_equisat_backward (before after : Prop) :
    AyVSPMEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vspm_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVSPMModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vspm_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vspm_model_formula (formula assignment : Prop) :
    AyVSPMModel formula assignment -> formula :=
  fun model => ay_vspm_conj_left formula assignment model

theorem ay_vspm_model_assignment (formula assignment : Prop) :
    AyVSPMModel formula assignment -> assignment :=
  fun model => ay_vspm_conj_right formula assignment model

theorem ay_vspm_policy_manifest_intro
    (manifestId selectedPolicy preprocessingProfile fingerprint : Prop) :
    manifestId -> selectedPolicy -> preprocessingProfile -> fingerprint ->
    AyVSPMPolicyManifest manifestId selectedPolicy preprocessingProfile
      fingerprint :=
  fun manifestProof policyProof profileProof fingerprintProof =>
    ay_vspm_conj_intro manifestId
      (AyVSPMConj selectedPolicy
        (AyVSPMConj preprocessingProfile fingerprint))
      manifestProof
      (ay_vspm_conj_intro selectedPolicy
        (AyVSPMConj preprocessingProfile fingerprint)
        policyProof
        (ay_vspm_conj_intro preprocessingProfile fingerprint profileProof
          fingerprintProof))

theorem ay_vspm_policy_manifest_policy
    (manifestId selectedPolicy preprocessingProfile fingerprint : Prop) :
    AyVSPMPolicyManifest manifestId selectedPolicy preprocessingProfile
      fingerprint ->
    selectedPolicy :=
  fun manifest =>
    ay_vspm_conj_right manifestId
      (AyVSPMConj selectedPolicy
        (AyVSPMConj preprocessingProfile fingerprint))
      manifest selectedPolicy (fun policyProof _tail => policyProof)

theorem ay_vspm_run_evidence_intro
    (benchmarkEvidence checkerReplay formulaFingerprint publicEvidence :
      Prop) :
    benchmarkEvidence -> checkerReplay -> formulaFingerprint ->
    publicEvidence ->
    AyVSPMRunEvidence benchmarkEvidence checkerReplay formulaFingerprint
      publicEvidence :=
  fun benchmarkProof replayProof fingerprintProof publicProof =>
    ay_vspm_conj_intro benchmarkEvidence
      (AyVSPMConj checkerReplay
        (AyVSPMConj formulaFingerprint publicEvidence))
      benchmarkProof
      (ay_vspm_conj_intro checkerReplay
        (AyVSPMConj formulaFingerprint publicEvidence)
        replayProof
        (ay_vspm_conj_intro formulaFingerprint publicEvidence
          fingerprintProof publicProof))

theorem ay_vspm_run_evidence_replay
    (benchmarkEvidence checkerReplay formulaFingerprint publicEvidence :
      Prop) :
    AyVSPMRunEvidence benchmarkEvidence checkerReplay formulaFingerprint
      publicEvidence ->
    checkerReplay :=
  fun evidence =>
    ay_vspm_conj_right benchmarkEvidence
      (AyVSPMConj checkerReplay
        (AyVSPMConj formulaFingerprint publicEvidence))
      evidence checkerReplay (fun replayProof _tail => replayProof)

theorem ay_vspm_run_evidence_public
    (benchmarkEvidence checkerReplay formulaFingerprint publicEvidence :
      Prop) :
    AyVSPMRunEvidence benchmarkEvidence checkerReplay formulaFingerprint
      publicEvidence ->
    publicEvidence :=
  fun evidence =>
    ay_vspm_conj_right benchmarkEvidence
      (AyVSPMConj checkerReplay
        (AyVSPMConj formulaFingerprint publicEvidence))
      evidence publicEvidence
      (fun _replayProof tail =>
        tail publicEvidence
          (fun _fingerprintProof publicProof => publicProof))

theorem ay_vspm_manifest_agreement_intro
    (manifestMatch benchmarkMatch replayMatch fingerprintMatch publicMatch :
      Prop) :
    manifestMatch -> benchmarkMatch -> replayMatch -> fingerprintMatch ->
    publicMatch ->
    AyVSPMManifestAgreement manifestMatch benchmarkMatch replayMatch
      fingerprintMatch publicMatch :=
  fun manifestProof benchmarkProof replayProof fingerprintProof publicProof =>
    ay_vspm_conj_intro manifestMatch
      (AyVSPMConj benchmarkMatch
        (AyVSPMConj replayMatch
          (AyVSPMConj fingerprintMatch publicMatch)))
      manifestProof
      (ay_vspm_conj_intro benchmarkMatch
        (AyVSPMConj replayMatch
          (AyVSPMConj fingerprintMatch publicMatch))
        benchmarkProof
        (ay_vspm_conj_intro replayMatch
          (AyVSPMConj fingerprintMatch publicMatch)
          replayProof
          (ay_vspm_conj_intro fingerprintMatch publicMatch
            fingerprintProof publicProof)))

theorem ay_vspm_manifest_agreement_replay
    (manifestMatch benchmarkMatch replayMatch fingerprintMatch publicMatch :
      Prop) :
    AyVSPMManifestAgreement manifestMatch benchmarkMatch replayMatch
      fingerprintMatch publicMatch ->
    replayMatch :=
  fun agreement =>
    ay_vspm_conj_right manifestMatch
      (AyVSPMConj benchmarkMatch
        (AyVSPMConj replayMatch
          (AyVSPMConj fingerprintMatch publicMatch)))
      agreement replayMatch
      (fun _benchmarkProof tail =>
        tail replayMatch (fun replayProof _tail2 => replayProof))

theorem ay_vspm_manifest_agreement_public
    (manifestMatch benchmarkMatch replayMatch fingerprintMatch publicMatch :
      Prop) :
    AyVSPMManifestAgreement manifestMatch benchmarkMatch replayMatch
      fingerprintMatch publicMatch ->
    publicMatch :=
  fun agreement =>
    ay_vspm_conj_right manifestMatch
      (AyVSPMConj benchmarkMatch
        (AyVSPMConj replayMatch
          (AyVSPMConj fingerprintMatch publicMatch)))
      agreement publicMatch
      (fun _benchmarkProof tail =>
        tail publicMatch
          (fun _replayProof tail2 =>
            tail2 publicMatch
              (fun _fingerprintProof publicProof => publicProof)))

theorem ay_vspm_sequential_selection_intro
    (policyManifest runEvidence manifestAgreement selectedRun : Prop) :
    policyManifest -> runEvidence -> manifestAgreement -> selectedRun ->
    AyVSPMSequentialSelection policyManifest runEvidence
      manifestAgreement selectedRun :=
  fun manifestProof evidenceProof agreementProof runProof =>
    ay_vspm_conj_intro policyManifest
      (AyVSPMConj runEvidence
        (AyVSPMConj manifestAgreement selectedRun))
      manifestProof
      (ay_vspm_conj_intro runEvidence
        (AyVSPMConj manifestAgreement selectedRun)
        evidenceProof
        (ay_vspm_conj_intro manifestAgreement selectedRun agreementProof
          runProof))

theorem ay_vspm_sequential_selection_manifest
    (policyManifest runEvidence manifestAgreement selectedRun : Prop) :
    AyVSPMSequentialSelection policyManifest runEvidence manifestAgreement
      selectedRun ->
    policyManifest :=
  fun selection =>
    ay_vspm_conj_left policyManifest
      (AyVSPMConj runEvidence
        (AyVSPMConj manifestAgreement selectedRun))
      selection

theorem ay_vspm_sequential_selection_evidence
    (policyManifest runEvidence manifestAgreement selectedRun : Prop) :
    AyVSPMSequentialSelection policyManifest runEvidence manifestAgreement
      selectedRun ->
    runEvidence :=
  fun selection =>
    ay_vspm_conj_right policyManifest
      (AyVSPMConj runEvidence
        (AyVSPMConj manifestAgreement selectedRun))
      selection runEvidence (fun evidenceProof _tail => evidenceProof)

theorem ay_vspm_sequential_selection_agreement
    (policyManifest runEvidence manifestAgreement selectedRun : Prop) :
    AyVSPMSequentialSelection policyManifest runEvidence manifestAgreement
      selectedRun ->
    manifestAgreement :=
  fun selection =>
    ay_vspm_conj_right policyManifest
      (AyVSPMConj runEvidence
        (AyVSPMConj manifestAgreement selectedRun))
      selection manifestAgreement
      (fun _evidenceProof tail =>
        tail manifestAgreement (fun agreementProof _runProof =>
          agreementProof))

theorem ay_vspm_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVSPMEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vspm_conj_intro exitCode
      (AyVSPMConj artifacts
        (AyVSPMConj checkerDecision (AyVSPMConj auditDigest diagnostic)))
      exitProof
      (ay_vspm_conj_intro artifacts
        (AyVSPMConj checkerDecision (AyVSPMConj auditDigest diagnostic))
        artifactsProof
        (ay_vspm_conj_intro checkerDecision
          (AyVSPMConj auditDigest diagnostic)
          checkerProof
          (ay_vspm_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vspm_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVSPMEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vspm_conj_right exitCode
      (AyVSPMConj artifacts
        (AyVSPMConj checkerDecision (AyVSPMConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vspm_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVSPMMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vspm_conj_intro leafHash (AyVSPMConj root entry)
      leafProof
      (ay_vspm_conj_intro root entry rootProof entryProof)

theorem ay_vspm_membership_entry (leafHash root entry : Prop) :
    AyVSPMMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vspm_conj_right leafHash (AyVSPMConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vspm_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVSPMNoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vspm_conj_intro reason (AyVSPMConj auditDigest diagnostic)
      reasonProof
      (ay_vspm_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vspm_fallback_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVSPMFallback reason auditDigest diagnostic :=
  ay_vspm_no_claim_intro reason auditDigest diagnostic

theorem ay_vspm_fallback_no_claim
    (reason auditDigest diagnostic : Prop) :
    AyVSPMFallback reason auditDigest diagnostic ->
    AyVSPMNoClaim reason auditDigest diagnostic :=
  fun fallback => fallback

theorem ay_vspm_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVSPMPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVSPMModel solver internalAssignment ->
    AyVSPMVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vspm_model_intro original visibleAssignment
      (ay_vspm_equisat_backward original solver preprocess
        (ay_vspm_model_formula solver internalAssignment model))
      (decode (ay_vspm_model_assignment solver internalAssignment model))

theorem ay_vspm_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVSPMPreprocessArtifact original solver ->
    AyVSPMUnsat solver ->
    AyVSPMUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vspm_equisat_forward original solver preprocess originalProof)

theorem ay_vspm_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVSPMPreprocessArtifact original solver ->
    AyVSPMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVSPMUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vspm_equisat_forward original solver preprocess originalProof))

theorem ay_vspm_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVSPMPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVSPMModel solver internalAssignment) ->
    AyVSPMMembership leafHash root
      (AyVSPMEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVSPMVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vspm_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vspm_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vspm_membership_entry leafHash root
            (AyVSPMEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vspm_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVSPMPreprocessArtifact original solver ->
    AyVSPMReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVSPMMembership leafHash root
      (AyVSPMEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVSPMUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vspm_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vspm_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vspm_membership_entry leafHash root
            (AyVSPMEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vspm_valid_selection_public_sound
    (policyManifest runEvidence manifestAgreement selectedRun
      satFact unsatFact noClaim : Prop) :
    AyVSPMSequentialSelection policyManifest runEvidence manifestAgreement
      selectedRun ->
    (policyManifest -> runEvidence -> manifestAgreement ->
      AyVSPMPublicResult satFact unsatFact noClaim) ->
    AyVSPMPublicResult satFact unsatFact noClaim :=
  fun selection sound =>
    sound
      (ay_vspm_sequential_selection_manifest policyManifest runEvidence
        manifestAgreement selectedRun selection)
      (ay_vspm_sequential_selection_evidence policyManifest runEvidence
        manifestAgreement selectedRun selection)
      (ay_vspm_sequential_selection_agreement policyManifest runEvidence
        manifestAgreement selectedRun selection)

theorem ay_vspm_valid_selection_preserves_sat
    (policyManifest runEvidence manifestAgreement selectedRun satFact :
      Prop) :
    AyVSPMSequentialSelection policyManifest runEvidence manifestAgreement
      selectedRun ->
    (runEvidence -> manifestAgreement -> satFact) ->
    satFact :=
  fun selection sound =>
    sound
      (ay_vspm_sequential_selection_evidence policyManifest runEvidence
        manifestAgreement selectedRun selection)
      (ay_vspm_sequential_selection_agreement policyManifest runEvidence
        manifestAgreement selectedRun selection)

theorem ay_vspm_valid_selection_preserves_unsat
    (policyManifest runEvidence manifestAgreement selectedRun unsatFact :
      Prop) :
    AyVSPMSequentialSelection policyManifest runEvidence manifestAgreement
      selectedRun ->
    (runEvidence -> manifestAgreement -> unsatFact) ->
    unsatFact :=
  fun selection sound =>
    sound
      (ay_vspm_sequential_selection_evidence policyManifest runEvidence
        manifestAgreement selectedRun selection)
      (ay_vspm_sequential_selection_agreement policyManifest runEvidence
        manifestAgreement selectedRun selection)

theorem ay_vspm_stale_profile_no_claim
    (staleProfile auditDigest diagnostic : Prop) :
    staleProfile -> auditDigest -> diagnostic ->
    AyVSPMNoClaim staleProfile auditDigest diagnostic :=
  ay_vspm_no_claim_intro staleProfile auditDigest diagnostic

theorem ay_vspm_wrong_manifest_no_claim
    (wrongManifest auditDigest diagnostic : Prop) :
    wrongManifest -> auditDigest -> diagnostic ->
    AyVSPMNoClaim wrongManifest auditDigest diagnostic :=
  ay_vspm_no_claim_intro wrongManifest auditDigest diagnostic

theorem ay_vspm_fallback_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVSPMFallback reason auditDigest diagnostic ->
    AyVSPMPublicResult satFact unsatFact
      (AyVSPMNoClaim reason auditDigest diagnostic) :=
  fun fallback =>
    ay_vspm_disj_right satFact
      (AyVSPMDisj unsatFact
        (AyVSPMNoClaim reason auditDigest diagnostic))
      (ay_vspm_disj_right unsatFact
        (AyVSPMNoClaim reason auditDigest diagnostic)
        (ay_vspm_fallback_no_claim reason auditDigest diagnostic fallback))

theorem ay_vspm_stale_or_wrong_manifest_fallback
    (staleProfile wrongManifest auditDigest diagnostic fallback : Prop) :
    AyVSPMDisj staleProfile wrongManifest ->
    auditDigest -> diagnostic ->
    (staleProfile -> AyVSPMFallback staleProfile auditDigest diagnostic ->
      fallback) ->
    (wrongManifest -> AyVSPMFallback wrongManifest auditDigest diagnostic ->
      fallback) ->
    fallback :=
  fun failure auditProof diagnosticProof onStale onWrong =>
    failure fallback
      (fun staleProof =>
        onStale staleProof
          (ay_vspm_fallback_intro staleProfile auditDigest diagnostic
            staleProof auditProof diagnosticProof))
      (fun wrongProof =>
        onWrong wrongProof
          (ay_vspm_fallback_intro wrongManifest auditDigest diagnostic
            wrongProof auditProof diagnosticProof))
