-- SAT-COMP validator manifest artifact-index soundness core.
--
-- Public result validation may load model, proof, or preprocessing artifacts
-- from a manifest index only when membership, kind, digest, fingerprint, run
-- id, and checker evidence agree.  Missing or mismatched artifacts are
-- no-claim recomputation obligations.

def AyVMAIConj (left right : Prop) : Prop :=
  forall result : Prop, (left -> right -> result) -> result

def AyVMAIDisj (left right : Prop) : Prop :=
  forall result : Prop, (left -> result) -> (right -> result) -> result

def AyVMAIEquisat (before after : Prop) : Prop :=
  AyVMAIConj (before -> after) (after -> before)

def AyVMAIPublicResult (satFact unsatFact noClaim : Prop) : Prop :=
  AyVMAIDisj satFact (AyVMAIDisj unsatFact noClaim)

def AyVMAIIndexEntry
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) : Prop :=
  AyVMAIConj entryMember
    (AyVMAIConj artifactKind
      (AyVMAIConj digestMatch
        (AyVMAIConj fingerprintMatch
          (AyVMAIConj runIdMatch checkerEvidence))))

def AyVMAIManifestIndex
    (manifestId indexDigest indexEntry : Prop) : Prop :=
  AyVMAIConj manifestId (AyVMAIConj indexDigest indexEntry)

def AyVMAILoadedArtifact
    (manifestIndex indexEntry artifactPayload : Prop) : Prop :=
  AyVMAIConj manifestIndex (AyVMAIConj indexEntry artifactPayload)

def AyVMAIEntry
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    Prop :=
  AyVMAIConj exitCode
    (AyVMAIConj artifacts
      (AyVMAIConj checkerDecision
        (AyVMAIConj auditDigest diagnostic)))

def AyVMAIMembership (leafHash root entry : Prop) : Prop :=
  AyVMAIConj leafHash (AyVMAIConj root entry)

def AyVMAINoClaim (reason auditDigest diagnostic : Prop) : Prop :=
  AyVMAIConj reason (AyVMAIConj auditDigest diagnostic)

def AyVMAIRecomputeObligation
    (reason auditDigest diagnostic : Prop) : Prop :=
  AyVMAIConj reason (AyVMAIConj auditDigest diagnostic)

def AyVMAIModel (formula assignment : Prop) : Prop :=
  AyVMAIConj formula assignment

def AyVMAIUnsat (formula : Prop) : Prop :=
  formula -> False

def AyVMAIVisibleSAT (original visibleAssignment : Prop) : Prop :=
  AyVMAIModel original visibleAssignment

def AyVMAIPreprocessArtifact (original solver : Prop) : Prop :=
  AyVMAIEquisat original solver

def AyVMAIReplayAccepted (solver stream finalClause : Prop) : Prop :=
  stream -> solver -> finalClause

theorem ay_vmai_conj_intro (left right : Prop) :
    left -> right -> AyVMAIConj left right :=
  fun hleft hright result build => build hleft hright

theorem ay_vmai_conj_left (left right : Prop) :
    AyVMAIConj left right -> left :=
  fun pair => pair left (fun hleft _hright => hleft)

theorem ay_vmai_conj_right (left right : Prop) :
    AyVMAIConj left right -> right :=
  fun pair => pair right (fun _hleft hright => hright)

theorem ay_vmai_disj_right (left right : Prop) :
    right -> AyVMAIDisj left right :=
  fun hright result _onLeft onRight => onRight hright

theorem ay_vmai_equisat_forward (before after : Prop) :
    AyVMAIEquisat before after -> before -> after :=
  fun witness hbefore =>
    witness after (fun forward _backward => forward hbefore)

theorem ay_vmai_equisat_backward (before after : Prop) :
    AyVMAIEquisat before after -> after -> before :=
  fun witness hafter =>
    witness before (fun _forward backward => backward hafter)

theorem ay_vmai_model_intro (formula assignment : Prop) :
    formula -> assignment -> AyVMAIModel formula assignment :=
  fun formulaProof assignmentProof =>
    ay_vmai_conj_intro formula assignment formulaProof assignmentProof

theorem ay_vmai_model_formula (formula assignment : Prop) :
    AyVMAIModel formula assignment -> formula :=
  fun model => ay_vmai_conj_left formula assignment model

theorem ay_vmai_model_assignment (formula assignment : Prop) :
    AyVMAIModel formula assignment -> assignment :=
  fun model => ay_vmai_conj_right formula assignment model

theorem ay_vmai_index_entry_intro
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) :
    entryMember -> artifactKind -> digestMatch -> fingerprintMatch ->
    runIdMatch -> checkerEvidence ->
    AyVMAIIndexEntry entryMember artifactKind digestMatch fingerprintMatch
      runIdMatch checkerEvidence :=
  fun memberProof kindProof digestProof fingerprintProof runProof
      checkerProof =>
    ay_vmai_conj_intro entryMember
      (AyVMAIConj artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))))
      memberProof
      (ay_vmai_conj_intro artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence)))
        kindProof
        (ay_vmai_conj_intro digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))
          digestProof
          (ay_vmai_conj_intro fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence)
            fingerprintProof
            (ay_vmai_conj_intro runIdMatch checkerEvidence runProof
              checkerProof))))

theorem ay_vmai_index_entry_member
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) :
    AyVMAIIndexEntry entryMember artifactKind digestMatch fingerprintMatch
      runIdMatch checkerEvidence ->
    entryMember :=
  fun entry =>
    ay_vmai_conj_left entryMember
      (AyVMAIConj artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))))
      entry

theorem ay_vmai_index_entry_kind
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) :
    AyVMAIIndexEntry entryMember artifactKind digestMatch fingerprintMatch
      runIdMatch checkerEvidence ->
    artifactKind :=
  fun entry =>
    ay_vmai_conj_right entryMember
      (AyVMAIConj artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))))
      entry artifactKind (fun kindProof _tail => kindProof)

theorem ay_vmai_index_entry_digest
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) :
    AyVMAIIndexEntry entryMember artifactKind digestMatch fingerprintMatch
      runIdMatch checkerEvidence ->
    digestMatch :=
  fun entry =>
    ay_vmai_conj_right entryMember
      (AyVMAIConj artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))))
      entry digestMatch
      (fun _kindProof tail =>
        tail digestMatch (fun digestProof _tail2 => digestProof))

theorem ay_vmai_index_entry_fingerprint
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) :
    AyVMAIIndexEntry entryMember artifactKind digestMatch fingerprintMatch
      runIdMatch checkerEvidence ->
    fingerprintMatch :=
  fun entry =>
    ay_vmai_conj_right entryMember
      (AyVMAIConj artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))))
      entry fingerprintMatch
      (fun _kindProof tail =>
        tail fingerprintMatch
          (fun _digestProof tail2 =>
            tail2 fingerprintMatch
              (fun fingerprintProof _tail3 => fingerprintProof)))

theorem ay_vmai_index_entry_run
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) :
    AyVMAIIndexEntry entryMember artifactKind digestMatch fingerprintMatch
      runIdMatch checkerEvidence ->
    runIdMatch :=
  fun entry =>
    ay_vmai_conj_right entryMember
      (AyVMAIConj artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))))
      entry runIdMatch
      (fun _kindProof tail =>
        tail runIdMatch
          (fun _digestProof tail2 =>
            tail2 runIdMatch
              (fun _fingerprintProof tail3 =>
                tail3 runIdMatch
                  (fun runProof _checkerProof => runProof))))

theorem ay_vmai_index_entry_checker
    (entryMember artifactKind digestMatch fingerprintMatch runIdMatch
      checkerEvidence : Prop) :
    AyVMAIIndexEntry entryMember artifactKind digestMatch fingerprintMatch
      runIdMatch checkerEvidence ->
    checkerEvidence :=
  fun entry =>
    ay_vmai_conj_right entryMember
      (AyVMAIConj artifactKind
        (AyVMAIConj digestMatch
          (AyVMAIConj fingerprintMatch
            (AyVMAIConj runIdMatch checkerEvidence))))
      entry checkerEvidence
      (fun _kindProof tail =>
        tail checkerEvidence
          (fun _digestProof tail2 =>
            tail2 checkerEvidence
              (fun _fingerprintProof tail3 =>
                tail3 checkerEvidence
                  (fun _runProof checkerProof => checkerProof))))

theorem ay_vmai_manifest_index_intro
    (manifestId indexDigest indexEntry : Prop) :
    manifestId -> indexDigest -> indexEntry ->
    AyVMAIManifestIndex manifestId indexDigest indexEntry :=
  fun manifestProof digestProof entryProof =>
    ay_vmai_conj_intro manifestId (AyVMAIConj indexDigest indexEntry)
      manifestProof
      (ay_vmai_conj_intro indexDigest indexEntry digestProof entryProof)

theorem ay_vmai_loaded_artifact_intro
    (manifestIndex indexEntry artifactPayload : Prop) :
    manifestIndex -> indexEntry -> artifactPayload ->
    AyVMAILoadedArtifact manifestIndex indexEntry artifactPayload :=
  fun manifestProof entryProof payloadProof =>
    ay_vmai_conj_intro manifestIndex
      (AyVMAIConj indexEntry artifactPayload)
      manifestProof
      (ay_vmai_conj_intro indexEntry artifactPayload entryProof
        payloadProof)

theorem ay_vmai_loaded_artifact_index_entry
    (manifestIndex indexEntry artifactPayload : Prop) :
    AyVMAILoadedArtifact manifestIndex indexEntry artifactPayload ->
    indexEntry :=
  fun loaded =>
    ay_vmai_conj_right manifestIndex
      (AyVMAIConj indexEntry artifactPayload)
      loaded indexEntry (fun entryProof _payloadProof => entryProof)

theorem ay_vmai_loaded_artifact_payload
    (manifestIndex indexEntry artifactPayload : Prop) :
    AyVMAILoadedArtifact manifestIndex indexEntry artifactPayload ->
    artifactPayload :=
  fun loaded =>
    ay_vmai_conj_right manifestIndex
      (AyVMAIConj indexEntry artifactPayload)
      loaded artifactPayload (fun _entryProof payloadProof =>
        payloadProof)

theorem ay_vmai_entry_intro
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    exitCode -> artifacts -> checkerDecision -> auditDigest -> diagnostic ->
    AyVMAIEntry exitCode artifacts checkerDecision auditDigest diagnostic :=
  fun exitProof artifactsProof checkerProof auditProof diagnosticProof =>
    ay_vmai_conj_intro exitCode
      (AyVMAIConj artifacts
        (AyVMAIConj checkerDecision (AyVMAIConj auditDigest diagnostic)))
      exitProof
      (ay_vmai_conj_intro artifacts
        (AyVMAIConj checkerDecision (AyVMAIConj auditDigest diagnostic))
        artifactsProof
        (ay_vmai_conj_intro checkerDecision
          (AyVMAIConj auditDigest diagnostic)
          checkerProof
          (ay_vmai_conj_intro auditDigest diagnostic auditProof
            diagnosticProof)))

theorem ay_vmai_entry_checker
    (exitCode artifacts checkerDecision auditDigest diagnostic : Prop) :
    AyVMAIEntry exitCode artifacts checkerDecision auditDigest diagnostic ->
    checkerDecision :=
  fun entry =>
    ay_vmai_conj_right exitCode
      (AyVMAIConj artifacts
        (AyVMAIConj checkerDecision (AyVMAIConj auditDigest diagnostic)))
      entry checkerDecision
      (fun _artifactsProof tail =>
        tail checkerDecision (fun checkerProof _auditTail => checkerProof))

theorem ay_vmai_membership_intro (leafHash root entry : Prop) :
    leafHash -> root -> entry -> AyVMAIMembership leafHash root entry :=
  fun leafProof rootProof entryProof =>
    ay_vmai_conj_intro leafHash (AyVMAIConj root entry)
      leafProof
      (ay_vmai_conj_intro root entry rootProof entryProof)

theorem ay_vmai_membership_entry (leafHash root entry : Prop) :
    AyVMAIMembership leafHash root entry -> entry :=
  fun membership =>
    ay_vmai_conj_right leafHash (AyVMAIConj root entry) membership
      entry (fun _rootProof entryProof => entryProof)

theorem ay_vmai_no_claim_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVMAINoClaim reason auditDigest diagnostic :=
  fun reasonProof auditProof diagnosticProof =>
    ay_vmai_conj_intro reason (AyVMAIConj auditDigest diagnostic)
      reasonProof
      (ay_vmai_conj_intro auditDigest diagnostic auditProof
        diagnosticProof)

theorem ay_vmai_recompute_intro
    (reason auditDigest diagnostic : Prop) :
    reason -> auditDigest -> diagnostic ->
    AyVMAIRecomputeObligation reason auditDigest diagnostic :=
  ay_vmai_no_claim_intro reason auditDigest diagnostic

theorem ay_vmai_preprocess_model_reconstruct
    (original solver internalAssignment visibleAssignment : Prop) :
    AyVMAIPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    AyVMAIModel solver internalAssignment ->
    AyVMAIVisibleSAT original visibleAssignment :=
  fun preprocess decode model =>
    ay_vmai_model_intro original visibleAssignment
      (ay_vmai_equisat_backward original solver preprocess
        (ay_vmai_model_formula solver internalAssignment model))
      (decode (ay_vmai_model_assignment solver internalAssignment model))

theorem ay_vmai_preprocess_unsat_reconstruct
    (original solver : Prop) :
    AyVMAIPreprocessArtifact original solver ->
    AyVMAIUnsat solver ->
    AyVMAIUnsat original :=
  fun preprocess solverUnsat originalProof =>
    solverUnsat
      (ay_vmai_equisat_forward original solver preprocess originalProof)

theorem ay_vmai_replay_unsat_public
    (original solver stream finalClause : Prop) :
    AyVMAIPreprocessArtifact original solver ->
    AyVMAIReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    stream ->
    AyVMAIUnsat original :=
  fun preprocess replay closeFinal streamProof originalProof =>
    closeFinal
      (replay streamProof
        (ay_vmai_equisat_forward original solver preprocess originalProof))

theorem ay_vmai_retained_sat_membership_sound
    (leafHash root acceptedSat artifacts satBranch auditDigest diagnostic
      original solver internalAssignment visibleAssignment : Prop) :
    AyVMAIPreprocessArtifact original solver ->
    (internalAssignment -> visibleAssignment) ->
    (satBranch -> AyVMAIModel solver internalAssignment) ->
    AyVMAIMembership leafHash root
      (AyVMAIEntry acceptedSat artifacts satBranch auditDigest diagnostic) ->
    AyVMAIVisibleSAT original visibleAssignment :=
  fun preprocess decode accept membership =>
    ay_vmai_preprocess_model_reconstruct original solver internalAssignment
      visibleAssignment preprocess decode
      (accept
        (ay_vmai_entry_checker acceptedSat artifacts satBranch auditDigest
          diagnostic
          (ay_vmai_membership_entry leafHash root
            (AyVMAIEntry acceptedSat artifacts satBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vmai_retained_unsat_membership_sound
    (leafHash root acceptedUnsat artifacts unsatBranch auditDigest diagnostic
      original solver stream finalClause : Prop) :
    AyVMAIPreprocessArtifact original solver ->
    AyVMAIReplayAccepted solver stream finalClause ->
    (finalClause -> False) ->
    (unsatBranch -> stream) ->
    AyVMAIMembership leafHash root
      (AyVMAIEntry acceptedUnsat artifacts unsatBranch auditDigest
        diagnostic) ->
    AyVMAIUnsat original :=
  fun preprocess replay closeFinal accept membership =>
    ay_vmai_replay_unsat_public original solver stream finalClause preprocess
      replay closeFinal
      (accept
        (ay_vmai_entry_checker acceptedUnsat artifacts unsatBranch
          auditDigest diagnostic
          (ay_vmai_membership_entry leafHash root
            (AyVMAIEntry acceptedUnsat artifacts unsatBranch auditDigest
              diagnostic)
            membership)))

theorem ay_vmai_loaded_artifact_public_sound
    (manifestIndex indexEntry artifactPayload satFact unsatFact noClaim :
      Prop) :
    AyVMAILoadedArtifact manifestIndex indexEntry artifactPayload ->
    (indexEntry -> artifactPayload ->
      AyVMAIPublicResult satFact unsatFact noClaim) ->
    AyVMAIPublicResult satFact unsatFact noClaim :=
  fun loaded sound =>
    sound
      (ay_vmai_loaded_artifact_index_entry manifestIndex indexEntry
        artifactPayload loaded)
      (ay_vmai_loaded_artifact_payload manifestIndex indexEntry
        artifactPayload loaded)

theorem ay_vmai_loaded_artifact_preserves_sat
    (manifestIndex indexEntry artifactPayload satFact : Prop) :
    AyVMAILoadedArtifact manifestIndex indexEntry artifactPayload ->
    (indexEntry -> artifactPayload -> satFact) ->
    satFact :=
  fun loaded sound =>
    sound
      (ay_vmai_loaded_artifact_index_entry manifestIndex indexEntry
        artifactPayload loaded)
      (ay_vmai_loaded_artifact_payload manifestIndex indexEntry
        artifactPayload loaded)

theorem ay_vmai_loaded_artifact_preserves_unsat
    (manifestIndex indexEntry artifactPayload unsatFact : Prop) :
    AyVMAILoadedArtifact manifestIndex indexEntry artifactPayload ->
    (indexEntry -> artifactPayload -> unsatFact) ->
    unsatFact :=
  fun loaded sound =>
    sound
      (ay_vmai_loaded_artifact_index_entry manifestIndex indexEntry
        artifactPayload loaded)
      (ay_vmai_loaded_artifact_payload manifestIndex indexEntry
        artifactPayload loaded)

theorem ay_vmai_missing_artifact_no_claim
    (missingArtifact auditDigest diagnostic : Prop) :
    missingArtifact -> auditDigest -> diagnostic ->
    AyVMAINoClaim missingArtifact auditDigest diagnostic :=
  ay_vmai_no_claim_intro missingArtifact auditDigest diagnostic

theorem ay_vmai_wrong_kind_no_claim
    (wrongKind auditDigest diagnostic : Prop) :
    wrongKind -> auditDigest -> diagnostic ->
    AyVMAINoClaim wrongKind auditDigest diagnostic :=
  ay_vmai_no_claim_intro wrongKind auditDigest diagnostic

theorem ay_vmai_wrong_digest_no_claim
    (wrongDigest auditDigest diagnostic : Prop) :
    wrongDigest -> auditDigest -> diagnostic ->
    AyVMAINoClaim wrongDigest auditDigest diagnostic :=
  ay_vmai_no_claim_intro wrongDigest auditDigest diagnostic

theorem ay_vmai_failure_public_result_no_claim
    (satFact unsatFact reason auditDigest diagnostic : Prop) :
    AyVMAINoClaim reason auditDigest diagnostic ->
    AyVMAIPublicResult satFact unsatFact
      (AyVMAINoClaim reason auditDigest diagnostic) :=
  fun noClaim =>
    ay_vmai_disj_right satFact
      (AyVMAIDisj unsatFact
        (AyVMAINoClaim reason auditDigest diagnostic))
      (ay_vmai_disj_right unsatFact
        (AyVMAINoClaim reason auditDigest diagnostic)
        noClaim)

theorem ay_vmai_missing_or_mismatched_recompute
    (missingArtifact wrongKind wrongDigest auditDigest diagnostic recompute :
      Prop) :
    AyVMAIDisj missingArtifact (AyVMAIDisj wrongKind wrongDigest) ->
    auditDigest -> diagnostic ->
    (missingArtifact ->
      AyVMAIRecomputeObligation missingArtifact auditDigest diagnostic ->
      recompute) ->
    (wrongKind ->
      AyVMAIRecomputeObligation wrongKind auditDigest diagnostic ->
      recompute) ->
    (wrongDigest ->
      AyVMAIRecomputeObligation wrongDigest auditDigest diagnostic ->
      recompute) ->
    recompute :=
  fun failure auditProof diagnosticProof onMissing onKind onDigest =>
    failure recompute
      (fun missingProof =>
        onMissing missingProof
          (ay_vmai_recompute_intro missingArtifact auditDigest diagnostic
            missingProof auditProof diagnosticProof))
      (fun tail =>
        tail recompute
          (fun kindProof =>
            onKind kindProof
              (ay_vmai_recompute_intro wrongKind auditDigest diagnostic
                kindProof auditProof diagnosticProof))
          (fun digestProof =>
            onDigest digestProof
              (ay_vmai_recompute_intro wrongDigest auditDigest diagnostic
                digestProof auditProof diagnosticProof)))
